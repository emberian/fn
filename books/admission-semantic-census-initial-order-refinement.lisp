; Actual BEGIN source-order law under the carried exact captured-target count.
; No runtime count scan, supplied row, or allocation authority.
(in-package "ACL2")
(include-book "admission-semantic-census-initial-refinement")
(include-book "snapshot-source-resident-lineage")
(include-book "admission-semantic-census-begin-refinement")
(include-book "../host/admission-semantic-census-host")

(local (defthm fn-rccap-order-prl-at-is-nth-by-definition
 (implies (natp n) (equal (fn-prl-nth n x) (nth n x)))
 :hints (("Goal" :induct (fn-prl-nth n x) :in-theory (enable fn-prl-nth nth)))))
(defthm fn-rccap-actual-begin-retains-captured-target-order
 (implies
  (and (eq (mv-nth 0 (fn-owner-admission-census-begin-logic fn-history-backing state)) :census-started)
       (equal target
        (fn-sfr-snoc (fn-sf-records-field (fn-sn-files
          (fn-prl-nth 5 (f-get-global 'fn-owner-canonical-admission-executor state))))
         (mv-nth 1 (fn-hep-builder-readout fn-history-backing))))
       (equal (1+ (fn-prl-nth 3 (f-get-global 'fn-owner-canonical-admission-executor state)))
              (+ (fn-rccos-base target) (len (fn-rccos-suffix target)))))
  (let* ((next (mv-nth 2 (fn-owner-admission-census-begin-logic fn-history-backing state)))
         (job (f-get-global 'fn-owner-history-semantic-census next)))
   (fn-rccos-cursor-invariantp (fn-prl-nth 2 job))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-owner-census-begin-establishes-retained-source-count
   (:instance fn-rccos-actual-begin-establishes-resident-suffix-lineage
     (field target)
     (count (1+ (fn-prl-nth 3 (f-get-global 'fn-owner-canonical-admission-executor state))))
     (epoch (fn-sf-frontier (fn-sn-files (fn-prl-nth 5 (f-get-global 'fn-owner-canonical-admission-executor state)))))
     (lease (list (fn-prl-nth 1 (fn-prl-nth 0 (fn-apr-owner-current state)))
                  (1+ (fn-prl-nth 3 (f-get-global 'fn-owner-canonical-admission-executor state)))))))
  :in-theory (e/d (fn-owner-admission-census-begin-logic)
   (fn-prl-nth fn-apr-owner-current fn-apr-tokenp fn-apr-livep fn-apr-widthp
    fn-owner-history-writer-gate fn-hep-builder-readout fn-hed-at fn-hep-builder fn-hep-producer-token
    fn-sn-files fn-sf-frontier fn-sf-records-field fn-sfr-snoc fn-osrc-begin fn-osrc-guardp fn-osrc-at
    fn-osm-begin fn-hct-begin fn-omk-at fn-evc-field-by-shape
    fn-rccos-cursor-invariantp fn-rccos-base fn-rccos-suffix boundp-global boundp-global1)))))

