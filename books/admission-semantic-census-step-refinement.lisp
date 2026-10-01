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

(defthm fn-rccap-actual-step-row-done-retains-extended-original-prefix
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
        (eq (mv-nth 0 (fn-hct-tick census)) :row-done))
   (and (equal (fn-prl-nth 1 next-job) token)
        (equal (fn-prl-nth 2 next-job) source)
        (equal (fn-prl-nth 3 next-job)
          (mv-nth 1 (fn-osm-census-ack remap (mv-nth 2 (fn-hct-tick census)))))
        (equal (fn-prl-nth 4 next-job) (mv-nth 2 (fn-hct-tick census)))
        (fn-rccap-idle-original-prefixp
          (fn-prl-nth 3 next-job) (fn-prl-nth 4 next-job)
          (append originals (list original))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-actual-ack-preserves-the-original-to-remapped-prefix
          (remapper (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state)
                   (f-get-global 'fn-owner-history-semantic-census state))))
          (census (fn-prl-nth 4 (and (boundp-global 'fn-owner-history-semantic-census state)
                   (f-get-global 'fn-owner-history-semantic-census state))))))
  :in-theory (e/d (fn-owner-admission-census-step-logic fn-hsrcb-demandp fn-prl-nth)
   (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp
    fn-owner-history-writer-gate fn-osrc-guardp fn-osrc-at fn-osrc-tick
    fn-omk-at fn-hct-tick fn-osm-census-ack fn-osm-prepare-row fn-hct-offer
    fn-rccap-waiting-original-prefixp fn-rccap-idle-original-prefixp)))))

(local (defthm fn-rccap-original-row-done-is-acknowledged
 (implies (and (fn-rccap-waiting-original-prefixp remapper census originals original row pool)
               (eq (mv-nth 0 (fn-hct-tick census)) :row-done))
  (eq (mv-nth 0 (fn-osm-census-ack remapper (mv-nth 2 (fn-hct-tick census))))
      :acknowledged))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rcca-actual-row-done-ack-advances-exactly-the-same-prefix
          (history (mv-nth 0 (fn-rccap-remapped-prefix originals 0)))))
  :in-theory (e/d (fn-rccap-waiting-original-prefixp)
   (fn-rcca-waiting-rowp fn-rccap-remapped-prefix fn-hct-tick fn-osm-census-ack))))))

(defthm fn-rccap-actual-step-row-done-acknowledges-and-retains-prefix
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
        (eq (mv-nth 0 (fn-hct-tick census)) :row-done))
   (and (eq (mv-nth 0 (fn-owner-admission-census-step-logic state)) :continue)
        (eq (fn-prl-nth 0 next-job) :history-census)
        (equal (fn-prl-nth 1 next-job) token)
        (equal (fn-prl-nth 2 next-job) source)
        (equal (fn-prl-nth 3 next-job)
          (mv-nth 1 (fn-osm-census-ack remap (mv-nth 2 (fn-hct-tick census)))))
        (equal (fn-prl-nth 4 next-job) (mv-nth 2 (fn-hct-tick census)))
        (fn-rccap-idle-original-prefixp
          (fn-prl-nth 3 next-job) (fn-prl-nth 4 next-job)
          (append originals (list original))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-original-row-done-is-acknowledged
          (remapper (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state))))
          (census (fn-prl-nth 4 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state)))))
        (:instance fn-rccap-actual-ack-preserves-the-original-to-remapped-prefix
          (remapper (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state)
                   (f-get-global 'fn-owner-history-semantic-census state))))
          (census (fn-prl-nth 4 (and (boundp-global 'fn-owner-history-semantic-census state)
                   (f-get-global 'fn-owner-history-semantic-census state))))))
  :in-theory (e/d (fn-owner-admission-census-step-logic fn-hsrcb-demandp fn-prl-nth)
   (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp
    fn-owner-history-writer-gate fn-osrc-guardp fn-osrc-at fn-osrc-tick
    fn-omk-at fn-hct-tick fn-osm-census-ack fn-osm-prepare-row fn-hct-offer
    fn-rccap-waiting-original-prefixp fn-rccap-idle-original-prefixp)))))

; Actual resident source packet association is explicit: this is the Tick
; result at the current source, not a supplied completion row or count.
(local (defthm fn-rccap-actual-fixed-row-prepare-unfolds
 (implies (and (fn-omk-tokenp expected)
               (equal ordinal (fn-omk-at 3 expected))
               (equal packet (list :row ordinal tagged expected next-source))
               (eq (car (mv-nth 0 (fn-osm-offer cursor expected tagged))) :mapped))
  (equal (fn-osm-prepare-row cursor packet)
    (mv :mapped
      (list :row ordinal (fn-omk-at 1 (mv-nth 0 (fn-osm-offer cursor expected tagged)))
            expected next-source)
      (mv-nth 1 (fn-osm-offer cursor expected tagged)))))
 :hints (("Goal" :in-theory (e/d (fn-osm-prepare-row fn-omk-at fn-omk-widthp)
                                  (fn-osm-offer fn-omk-tokenp))))))

(local (defthm fn-rccap-actual-offer-mapped-value-unfolds
 (implies (eq (car (mv-nth 0 (fn-osm-offer cursor token original))) :mapped)
  (equal (fn-omk-at 1 (mv-nth 0 (fn-osm-offer cursor token original)))
         (mv-nth 0 (fn-osm-row-source original (fn-omk-at 2 cursor)))))
 :hints (("Goal" :in-theory (e/d (fn-osm-offer fn-omk-at)
                     (fn-osm-row-source fn-omk-token-matchp fn-omk-widthp))))))

(defthm fn-rccap-actual-step-resident-offer-retains-original-prefix
 (let* ((current (fn-apr-owner-current state)) (token (fn-prl-nth 0 current))
        (job (and (boundp-global 'fn-owner-history-semantic-census state)
                  (f-get-global 'fn-owner-history-semantic-census state)))
        (source (fn-prl-nth 2 job)) (remapper (fn-prl-nth 3 job))
        (census (fn-prl-nth 4 job)) (expected (fn-omk-at 1 remapper))
        (mapped (mv-nth 0 (fn-osm-row-source (list :resident original)
                                            (fn-omk-at 2 remapper))))
        (row (fn-omk-at 1 mapped))
        (next-state (mv-nth 1 (fn-owner-admission-census-step-logic state)))
        (next-job (f-get-global 'fn-owner-history-semantic-census next-state)))
  (implies
   (and (fn-apr-tokenp token) (fn-apr-livep token current)
        (eq (fn-owner-history-writer-gate token state) :writer-current)
        (fn-apr-widthp 5 job) (eq (fn-prl-nth 0 job) :history-census)
        (fn-apr-tokenp (fn-prl-nth 1 job)) (equal token (fn-prl-nth 1 job))
        (eq (fn-omk-at 0 census) :need-row)
        (fn-osrc-guardp source) (not (eq (fn-osrc-at 0 source) :waiting))
        (equal (fn-osrc-tick source nil)
          (list :row (fn-omk-at 3 expected) (list :resident original) expected next-source))
        (fn-rccap-idle-original-prefixp remapper census originals)
        (fn-omk-widthp mapped 2)
        (natp (mv-nth 1 (fn-osm-row-source (list :resident original)
                                         (fn-omk-at 2 remapper))))
        (fn-hrcur-tree-domainp row)
        (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*)
        (eq (car (mv-nth 0 (fn-osm-offer remapper expected (list :resident original)))) :mapped))
   (and (equal (fn-prl-nth 1 next-job) token)
        (equal (fn-prl-nth 2 next-job) next-source)
        (fn-rccap-waiting-original-prefixp
          (fn-prl-nth 3 next-job) (fn-prl-nth 4 next-job)
          originals original row pool))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-actual-offer-mapped-value-unfolds
          (cursor (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state))))
          (token (fn-omk-at 1 (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state)))))
          (original (list :resident original)))
        (:instance fn-rccap-actual-fixed-row-prepare-unfolds
          (cursor (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state))))
          (expected (fn-omk-at 1 (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state)))))
          (ordinal (fn-omk-at 3 (fn-omk-at 1 (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state))))))
          (tagged (list :resident original))
          (packet (fn-osrc-tick (fn-prl-nth 2 (and (boundp-global 'fn-owner-history-semantic-census state) (f-get-global 'fn-owner-history-semantic-census state))) nil)))
        (:instance fn-rccap-actual-resident-offers-establish-original-prefix
          (remapper (fn-prl-nth 3 (and (boundp-global 'fn-owner-history-semantic-census state)
                         (f-get-global 'fn-owner-history-semantic-census state))))
          (census (fn-prl-nth 4 (and (boundp-global 'fn-owner-history-semantic-census state)
                         (f-get-global 'fn-owner-history-semantic-census state)))))
        (:instance fn-rccap-actual-remapped-prefix-keeps-row-count (rows originals) (handle 0)))
  :in-theory (e/d (fn-owner-admission-census-step-logic
                   fn-prl-nth fn-osrc-at fn-omk-at fn-rccap-idle-original-prefixp fn-rcca-idle-prefixp)
   (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp
    fn-owner-history-writer-gate fn-osrc-guardp fn-osrc-tick
    fn-osm-prepare-row fn-hct-tick fn-hct-offer fn-osm-census-ack fn-osm-offer fn-osm-row-source
    fn-rccap-waiting-original-prefixp fn-rccap-remapped-prefix fn-hp-pes-len
    fn-omk-tokenp fn-omk-widthp fn-hct-shapep fn-scc-encode)))))
