; Whole measured-prefix readout, no installed allocation/source authority.
(in-package "ACL2")
(include-book "snapshot-row-source-ack-refinement")
(include-book "owner-recovery-canonical-census")
(defthm fn-rcc-actual-measured-readout-is-the-carried-mapped-prefix
 (implies
  (and (fn-rcca-idle-prefixp remapper census mapped-history)
       (eq (mv-nth 0 (fn-rcc-readout collector source remapper census)) :measured))
  (let ((measured (mv-nth 1 (fn-rcc-readout collector source remapper census))))
   (and (equal (fn-omk-at 0 measured) :measured)
        (equal (fn-omk-at 2 measured) (len mapped-history))
        (equal (fn-omk-at 3 measured) (fn-hp-pes-len mapped-history))
        (equal (fn-omk-at 4 measured) (fn-omk-at 4 collector))
        (equal (fn-omk-at 5 measured) (fn-omk-at 5 collector))
        (equal (fn-omk-at 6 measured) (fn-omk-at 6 collector)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-rcca-idle-prefixp fn-rcc-readout fn-rcc-offer fn-omk-at)
                 (fn-rcc-state fn-hct-shapep fn-omk-widthp fn-omk-tokenp
                  fn-osrc-guardp fn-hp-pes-len len)))))
