; Exact logical STEP effects, not an alternate census transition.
(in-package "ACL2")
(include-book "../host/admission-semantic-census-host")
(include-book "admission-semantic-census-prefix")

(defthm fn-rccap-actual-step-retains-operation-and-source-globals
 (and
  (equal (fn-apr-owner-current
           (mv-nth 1 (fn-owner-admission-census-step-logic state)))
         (fn-apr-owner-current state))
  (equal (f-get-global 'fn-owner-canonical-admission-executor
           (mv-nth 1 (fn-owner-admission-census-step-logic state)))
         (f-get-global 'fn-owner-canonical-admission-executor state))
  (equal (f-get-global 'fn-owner-history-semantic-source
           (mv-nth 1 (fn-owner-admission-census-step-logic state)))
         (f-get-global 'fn-owner-history-semantic-source state)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-owner-admission-census-step-logic fn-apr-owner-current)
   (fn-apr-tokenp fn-apr-livep fn-apr-widthp fn-owner-history-writer-gate
    fn-prl-nth fn-osrc-guardp fn-osrc-at fn-osrc-tick fn-omk-at
    fn-hct-tick fn-hsrcb-demandp fn-osm-census-ack fn-osm-prepare-row fn-hct-offer)))))

; Invalid scalar preflight is a corrupted-state fence witness, not accepted
; Store lineage or an allocation allowance. The row is fetched from STATE.
(defthm fn-rccap-actual-step-fences-invalid-source-with-all-frames
 (let* ((current (fn-apr-owner-current state))
        (token (fn-prl-nth 0 current))
        (job (and (boundp-global 'fn-owner-history-semantic-census state)
                  (f-get-global 'fn-owner-history-semantic-census state)))
        (source (fn-prl-nth 2 job)) (remap (fn-prl-nth 3 job))
        (census (fn-prl-nth 4 job)))
  (implies
   (and (fn-apr-tokenp token) (fn-apr-livep token current)
        (eq (fn-owner-history-writer-gate token state) :writer-current)
        (fn-apr-widthp 5 job) (eq (fn-prl-nth 0 job) :history-census)
        (fn-apr-tokenp (fn-prl-nth 1 job))
        (equal token (fn-prl-nth 1 job))
        (eq (fn-omk-at 0 census) :need-row)
        (not (fn-osrc-guardp source)))
   (and
    (eq (mv-nth 0 (fn-owner-admission-census-step-logic state)) :recovery-required)
    (equal (f-get-global 'fn-owner-history-semantic-census
             (mv-nth 1 (fn-owner-admission-census-step-logic state)))
           (list :history-census-fenced token source remap census)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-owner-admission-census-step-logic)
   (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp
    fn-owner-history-writer-gate fn-prl-nth fn-osrc-guardp fn-osrc-at
    fn-osrc-tick fn-omk-at fn-hct-tick fn-hsrcb-demandp fn-osm-census-ack
    fn-osm-prepare-row fn-hct-offer)))))

; Join the already proved actual codec continuation to the registered slot.
(defthm fn-rccap-actual-step-codec-continue-preserves-original-prefix
 (let* ((current (fn-apr-owner-current state)) (token (fn-prl-nth 0 current))
        (job (and (boundp-global 'fn-owner-history-semantic-census state)
                  (f-get-global 'fn-owner-history-semantic-census state)))
        (source (fn-prl-nth 2 job)) (remap (fn-prl-nth 3 job))
        (census (fn-prl-nth 4 job))
        (next-state (mv-nth 1 (fn-owner-admission-census-step-logic state)))
        (next-job (f-get-global 'fn-owner-history-semantic-census next-state)))
  (implies
   (and (fn-apr-tokenp token) (fn-apr-livep token current)
        (eq (fn-owner-history-writer-gate token state) :writer-current)
        (fn-apr-widthp 5 job) (eq (fn-prl-nth 0 job) :history-census)
        (fn-apr-tokenp (fn-prl-nth 1 job)) (equal token (fn-prl-nth 1 job))
        (eq (fn-omk-at 0 census) :codec)
        (fn-rccap-waiting-original-prefixp remap census originals original row pool)
        (eq (mv-nth 0 (fn-hct-tick census)) :continue))
   (and (eq (mv-nth 0 (fn-owner-admission-census-step-logic state)) :continue)
        (equal next-job
          (list :history-census token source remap (mv-nth 2 (fn-hct-tick census))))
        (fn-rccap-waiting-original-prefixp
          (fn-prl-nth 3 next-job) (fn-prl-nth 4 next-job)
          originals original row pool))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-actual-codec-continue-retains-original-pending-prefix
          (remapper (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state)
                   (f-get-global 'fn-owner-history-semantic-census state))))
          (census (fn-prl-nth 4 (and (boundp-global 'fn-owner-history-semantic-census state)
                   (f-get-global 'fn-owner-history-semantic-census state))))))
  :in-theory (e/d (fn-owner-admission-census-step-logic fn-hsrcb-demandp fn-prl-nth)
   (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp
    fn-owner-history-writer-gate fn-osrc-guardp fn-osrc-at fn-osrc-tick
    fn-omk-at fn-hct-tick fn-osm-census-ack fn-osm-prepare-row fn-hct-offer
    fn-rccap-waiting-original-prefixp)))))
