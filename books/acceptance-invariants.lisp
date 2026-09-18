; Small, separately certified preservation facts for the acceptance machine.
; The successful allocation path needs additional watermark lemmas and is kept
; out of this bounded book until those lemmas are proved.

(in-package "ACL2")
(include-book "acceptance")

(defthm fn-prepare-fenced-preserves-state
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) t))
           (fn-statep
            (fn-accept-prepare s generation msgid payload groups)))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-prepare-duplicate-preserves-state
  (implies (and (fn-statep s)
                (fn-acceptedp msgid (fn-state-articles s)))
           (fn-statep
            (fn-accept-prepare s generation msgid payload groups)))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))

(defthm fn-complete-fenced-preserves-state
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) t))
           (fn-statep
            (fn-accept-complete s txid generation completion-status)))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-complete-stale-preserves-state
  (implies (and (fn-statep s)
                (not (fn-pending-matchesp (fn-state-pending s)
                                          txid generation)))
           (fn-statep
            (fn-accept-complete s txid generation completion-status)))
  :hints (("Goal" :in-theory (enable fn-accept-complete))))

(defthm fn-recover-stale-preserves-state
  (implies (and (fn-statep s)
                (or (not (equal (fn-state-fenced s) t))
                    (not (fn-pending-matchesp (fn-state-pending s)
                                              txid generation))))
           (fn-statep
            (fn-accept-recover s txid generation recovery-result)))
  :hints (("Goal" :in-theory (enable fn-accept-recover))))

(defthm fn-prepare-preserves-state-under-allocation-facts
  (implies (and (fn-statep s)
                (equal (fn-state-fenced s) nil)
                (null (fn-state-pending s))
                (natp generation)
                (stringp msgid)
                (fn-octet-listp payload)
                (fn-selection-validp groups (fn-state-groups s))
                (not (fn-acceptedp msgid (fn-state-articles s)))
                (fn-membership-listp
                 groups
                 (fn-allocate-memberships groups (fn-state-nexts s)))
                (fn-memberships-at-watermarkp
                 (fn-allocate-memberships groups (fn-state-nexts s))
                 (fn-state-nexts s)))
           (fn-statep
            (fn-accept-prepare s generation msgid payload groups)))
  :hints (("Goal" :in-theory (enable fn-accept-prepare fn-statep))))
