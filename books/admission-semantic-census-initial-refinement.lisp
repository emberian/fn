; Actual registered BEGIN establishes the initial remapped-prefix state.
; No supplied count/row/source readout and no allocator authority is added.
(in-package "ACL2")
(include-book "../host/admission-semantic-census-host")
(include-book "admission-semantic-census-prefix")
(local (defthm fn-rccap-hct-begin-not-refused-has-codec-count
 (implies (not (eq (fn-omk-at 0 (fn-hct-begin count capture resource)) :refused))
          (unsigned-byte-p 61 count))
 :hints (("Goal" :in-theory (enable fn-hct-begin fn-omk-at)))))
(local (defthm fn-rccap-fixed-initial-source-establishes-empty-prefix
 (implies (and (natp frontier) (natp nonce) (unsigned-byte-p 61 count))
  (fn-rccap-idle-original-prefixp
    (fn-osm-begin (list frontier (list nonce count) 0 0))
    (fn-hct-begin count (list nonce count) resource) nil))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-actual-begin-establishes-empty-original-prefix
          (source (list frontier (list nonce count) 0 0))))
  :in-theory (e/d (fn-omk-tokenp fn-omk-widthp fn-omk-at)
                  (fn-rccap-idle-original-prefixp fn-osm-begin fn-hct-begin))))))

(local (defthm fn-rccap-prl-at-is-nth-by-definition
 (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
 :hints (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))
(local (defthm fn-rccap-token-has-natural-nonce
 (implies (fn-apr-tokenp token) (natp (nth 1 token)))
 :hints (("Goal" :in-theory (enable fn-apr-tokenp fn-prl-nth)))))
(local (defthm fn-rccap-initial-source-lenses-by-definition
 (and (equal (fn-osrc-at 2 (fn-osrc-begin field count epoch lease)) 0)
      (equal (fn-osrc-token (fn-osrc-begin field count epoch lease))
             (list epoch lease 0 0)))
 :hints (("Goal" :in-theory (enable fn-osrc-token fn-osrc-begin fn-osrc-at)))))

(local (defthm fn-rccap-initial-remapper-source-by-definition
 (equal (fn-omk-at 1 (fn-osm-begin source)) source)
 :hints (("Goal" :in-theory (enable fn-osm-begin fn-omk-at)))))
(defthm fn-rccap-actual-owner-begin-establishes-registered-empty-prefix
 (implies (eq (mv-nth 0 (fn-owner-admission-census-begin-logic fn-history-backing state))
              :census-started)
  (let* ((next-state (mv-nth 2 (fn-owner-admission-census-begin-logic fn-history-backing state)))
         (job (f-get-global 'fn-owner-history-semantic-census next-state))
         (cursor (fn-prl-nth 2 job)) (remapper (fn-prl-nth 3 job))
         (census (fn-prl-nth 4 job)))
   (and (eq (fn-prl-nth 0 job) :history-census)
        (equal (fn-prl-nth 1 job) (fn-prl-nth 0 (fn-apr-owner-current state)))
        (equal (fn-osrc-at 2 cursor) 0)
        (equal (fn-osrc-token cursor) (fn-omk-at 1 remapper))
        (fn-rccap-idle-original-prefixp remapper census nil))))
 :rule-classes nil
  :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rccap-fixed-initial-source-establishes-empty-prefix
    (frontier (fn-sf-frontier (fn-sn-files (fn-prl-nth 5 (f-get-global 'fn-owner-canonical-admission-executor state)))))
    (nonce (fn-prl-nth 1 (fn-prl-nth 0 (fn-apr-owner-current state))))
    (count (1+ (fn-prl-nth 3 (f-get-global 'fn-owner-canonical-admission-executor state))))
    (resource (fn-prl-nth 0 (fn-apr-owner-current state))))
   (:instance fn-rccap-hct-begin-not-refused-has-codec-count
    (count (1+ (fn-prl-nth 3 (f-get-global 'fn-owner-canonical-admission-executor state))))
    (capture (list (fn-prl-nth 1 (fn-prl-nth 0 (fn-apr-owner-current state))) (1+ (fn-prl-nth 3 (f-get-global 'fn-owner-canonical-admission-executor state)))))
    (resource (fn-prl-nth 0 (fn-apr-owner-current state)))))
  :in-theory (e/d (fn-owner-admission-census-begin-logic)
   (unsigned-byte-p integer-range-p fn-prl-nth fn-apr-tokenp fn-osrc-token fn-osrc-at fn-omk-at
    boundp-global boundp-global1 fn-hep-builder fn-hep-producer-token
    fn-apr-owner-current fn-apr-livep fn-apr-widthp fn-owner-history-writer-gate
    fn-hep-builder-readout fn-hed-at fn-sn-files fn-sf-frontier fn-sf-records-field
    fn-sfr-snoc fn-osrc-begin fn-osm-begin fn-hct-begin fn-evc-field-by-shape
    fn-rccap-idle-original-prefixp)))))
