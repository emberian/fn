(in-package "ACL2")
(include-book "../host/admission-semantic-census-host")
(encapsulate ()
(local (defthm fn-owner-census-source-begin-count-by-definition
 (equal (fn-osrc-at 3 (fn-osrc-begin field count epoch lease)) count)
 :hints (("Goal" :in-theory (enable fn-osrc-at fn-osrc-begin)))))
(local (defthm fn-owner-census-prl-at-is-nth-by-definition
 (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
 :hints (("Goal" :induct (fn-prl-nth n x)
  :in-theory (enable fn-prl-nth nth)))))
(defthm fn-owner-census-begin-retains-original-intent
 (equal (f-get-global 'fn-owner-canonical-admission-executor
                      (mv-nth 2 (fn-owner-admission-census-begin-logic fn-history-backing state)))
        (f-get-global 'fn-owner-canonical-admission-executor state))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-owner-admission-census-begin-logic)
    (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp fn-prl-nth
     fn-owner-history-writer-gate fn-hep-builder-readout fn-hed-at fn-sn-files
     fn-sf-frontier fn-sfr-snoc fn-osrc-begin fn-osm-begin fn-hct-begin
     fn-evc-field-by-shape)))))
(defthm fn-owner-census-begin-establishes-retained-source-count
 (implies
  (equal (mv-nth 0 (fn-owner-admission-census-begin-logic fn-history-backing state))
         :census-started)
  (let* ((intent (f-get-global 'fn-owner-canonical-admission-executor state))
         (next (mv-nth 2 (fn-owner-admission-census-begin-logic fn-history-backing state)))
         (job (f-get-global 'fn-owner-history-semantic-census next))
         (source (fn-prl-nth 2 job)))
   (and (fn-osrc-guardp source)
        (equal (fn-osrc-at 3 source) (1+ (fn-prl-nth 3 intent)))
        (equal (fn-osrc-at 1 source)
               (fn-sfr-snoc (fn-sf-records-field (fn-sn-files (fn-prl-nth 5 intent)))
                            (mv-nth 1 (fn-hep-builder-readout fn-history-backing)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-owner-admission-census-begin-logic)
    (fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp fn-prl-nth
     fn-owner-history-writer-gate fn-hep-builder-readout fn-hed-at fn-sn-files
     fn-sf-frontier fn-sf-records-field fn-sfr-snoc fn-osrc-begin fn-osrc-guardp fn-osrc-at fn-osm-begin fn-hct-begin
     fn-evc-field-by-shape)))))
)
