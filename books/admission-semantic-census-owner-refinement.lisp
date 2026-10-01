; Actual registered readout composition. This is a proof companion, never a
; served source validator. Current STATE/target establishment remains an
; actual producer obligation; neither job shape nor scalar completion proves it.
(in-package "ACL2")
(include-book "admission-semantic-census-prefix")
(include-book "../host/admission-semantic-census-host")

; Low actual readout boundary over the retained selected-prefix relation.
; TARGET is a ghost value; the public readout still takes only actual STATE.
(defun-nx fn-rccap-owner-selected-prefixp (target state)
 (declare (xargs :stobjs state :verify-guards nil))
 (let* ((job (and (boundp-global 'fn-owner-history-semantic-census state)
                  (f-get-global 'fn-owner-history-semantic-census state)))
        (cursor (fn-prl-nth 2 job)) (remapper (fn-prl-nth 3 job))
        (census (fn-prl-nth 4 job)) (ordinal (fn-osrc-at 2 cursor)))
  (and (true-listp target) (equal ordinal (len target))
       (fn-rccap-idle-original-prefixp remapper census (take ordinal target)))))

(defthm fn-rccap-owner-readout-refines-the-retained-selected-prefix
 (implies (and (fn-rccap-owner-selected-prefixp target state)
               (eq (mv-nth 0 (fn-owner-admission-census-result state)) :census-prepared))
  (and (equal (mv-nth 1 (fn-owner-admission-census-result state))
                (fn-hp-pes-len (mv-nth 0 (fn-rccap-remapped-prefix target 0))))
       (equal (mv-nth 2 (fn-owner-admission-census-result state)) (len target))
       (equal (fn-omk-at 3 (mv-nth 3 (fn-owner-admission-census-result state)))
                (len target))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-terminal-selected-target-has-exact-count-and-pool
         (ordinal (fn-osrc-at 2 (fn-prl-nth 2
          (and (boundp-global 'fn-owner-history-semantic-census state)
               (f-get-global 'fn-owner-history-semantic-census state)))))
         (remapper (fn-prl-nth 3
          (and (boundp-global 'fn-owner-history-semantic-census state)
               (f-get-global 'fn-owner-history-semantic-census state))))
         (census (fn-prl-nth 4
          (and (boundp-global 'fn-owner-history-semantic-census state)
               (f-get-global 'fn-owner-history-semantic-census state))))))
  :in-theory (e/d (fn-rccap-owner-selected-prefixp fn-owner-admission-census-result)
                  (fn-rccap-idle-original-prefixp fn-rccap-remapped-prefix
                   fn-apr-owner-current fn-prl-nth fn-osrc-at fn-omk-at
                   fn-owner-history-writer-gate fn-sn-files fn-sf-frontier fn-hp-pes-len)))))

(defun-nx fn-rccap-owner-selected-targetp (candidate state)
 (declare (xargs :stobjs state :verify-guards nil))
 (let* ((intent (and (boundp-global 'fn-owner-canonical-admission-executor state)
                     (f-get-global 'fn-owner-canonical-admission-executor state)))
        (job (and (boundp-global 'fn-owner-history-semantic-census state)
                  (f-get-global 'fn-owner-history-semantic-census state)))
        (cursor (fn-prl-nth 2 job)) (remapper (fn-prl-nth 3 job))
        (census (fn-prl-nth 4 job))
        (files (fn-sn-files (fn-prl-nth 5 intent)))
        (field (fn-sfr-snoc (fn-sf-records-field files) candidate))
        (target (fn-sfr-list field)) (ordinal (fn-osrc-at 2 cursor)))
  (and (equal (fn-osrc-at 1 cursor) field)
       (true-listp target)
       (equal ordinal (len target))
       (fn-rccap-idle-original-prefixp remapper census (take ordinal target)))))

; The antecedent is the maintained SAME target/prefix relation, not a runtime
; traversal. Actual BEGIN/STEP establishment at the registered slot and the
; physical decoded source association are separate, still-open obligations.
(defthm fn-rccap-owner-census-readout-is-the-selected-remapped-target
 (implies
  (and (fn-rccap-owner-selected-targetp candidate state)
       (eq (mv-nth 0 (fn-owner-admission-census-result state)) :census-prepared))
  (let* ((intent (and (boundp-global 'fn-owner-canonical-admission-executor state)
                      (f-get-global 'fn-owner-canonical-admission-executor state)))
         (files (fn-sn-files (fn-prl-nth 5 intent)))
         (target (fn-sfr-list (fn-sfr-snoc (fn-sf-records-field files) candidate)))
         (answer (fn-owner-admission-census-result state)))
   (and (equal (mv-nth 1 answer)
                (fn-hp-pes-len (mv-nth 0 (fn-rccap-remapped-prefix target 0))))
        (equal (mv-nth 2 answer) (len target))
        (equal (fn-omk-at 3 (mv-nth 3 answer)) (len target)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-terminal-selected-target-has-exact-count-and-pool
         (target (fn-sfr-list
          (fn-sfr-snoc
           (fn-sf-records-field
            (fn-sn-files (fn-prl-nth 5
             (and (boundp-global 'fn-owner-canonical-admission-executor state)
                  (f-get-global 'fn-owner-canonical-admission-executor state))))) candidate)))
         (ordinal (fn-osrc-at 2 (fn-prl-nth 2
          (and (boundp-global 'fn-owner-history-semantic-census state)
               (f-get-global 'fn-owner-history-semantic-census state)))))
         (remapper (fn-prl-nth 3
          (and (boundp-global 'fn-owner-history-semantic-census state)
               (f-get-global 'fn-owner-history-semantic-census state))))
         (census (fn-prl-nth 4
          (and (boundp-global 'fn-owner-history-semantic-census state)
               (f-get-global 'fn-owner-history-semantic-census state))))))
  :in-theory (e/d (fn-rccap-owner-selected-targetp fn-owner-admission-census-result)
                  (fn-rccap-idle-original-prefixp fn-rccap-remapped-prefix
                   fn-apr-owner-current fn-prl-nth fn-osrc-at fn-omk-at
                   fn-owner-history-writer-gate fn-sfr-snoc fn-sfr-list
                   fn-sf-records-field fn-sn-files fn-sf-frontier fn-hp-pes-len)))))
