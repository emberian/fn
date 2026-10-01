; Actual source readout and cancellation effects. These laws do not assert
; a qualified constructor, installed Store correspondence or native authority.
(in-package "ACL2")
(include-book "history-source-capture")
(defthm fn-owner-history-source-attributes-exact-current-and-owner-epoch
 (implies (equal (mv-nth 0 (fn-owner-history-source fn-history-backing state)) :source)
  (and (equal (mv-nth 1 (fn-owner-history-source fn-history-backing state))
              (fn-hep-current fn-history-backing))
       (fn-hhc-sourcep (fn-hep-current fn-history-backing))
       (posp (fn-hhc-at 2 (fn-hep-current fn-history-backing)))
       (natp (fn-owner-canonical-epoch state))
       (fn-hhc-widthp (fn-owner-history-publication state) 6)
       (equal (fn-hhc-at 0 (fn-owner-history-publication state)) :history-installed)
       (equal (fn-hhc-at 1 (fn-owner-history-publication state))
              (fn-hhc-at 1 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 2 (fn-owner-history-publication state))
              (fn-hhc-at 2 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 3 (fn-owner-history-publication state))
              (fn-hhc-at 3 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 4 (fn-owner-history-publication state))
              (fn-hhc-at 8 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 5 (fn-owner-history-publication state))
              (fn-owner-canonical-epoch state))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-owner-history-source)
                  (fn-owner-history-publication fn-owner-canonical-epoch
                   fn-hep-current fn-hhc-sourcep fn-hhc-widthp fn-hhc-at)))))
(defthm fn-owner-history-source-refuses-old-parent-epoch-by-definition
 (implies (and (fn-owner-history-publication state)
                (fn-hep-current fn-history-backing)
                (not (equal (fn-hhc-at 5 (fn-owner-history-publication state))
                            (fn-owner-canonical-epoch state))))
  (equal (fn-owner-history-source fn-history-backing state)
         (mv :recovery-required nil)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-owner-history-source)
                  (fn-owner-history-publication fn-owner-canonical-epoch
                   fn-hep-current fn-hhc-sourcep fn-hhc-widthp fn-hhc-at)))))
; Cancellation retains read aliases and prevents another bounded action.
(defthm fn-owner-history-nonretained-read-refuses-without-state-effects
 (implies (not (equal (fn-hhc-at 5 (fn-owner-history-capture-slot state)) :retained))
  (equal (fn-owner-history-read-step fuel fn-history-backing state)
         (mv :history-source-stale nil (nfix fuel) state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
             (fn-owner-history-read-step fn-owner-history-read-plan
              fn-hhc-read-plan fn-hhc-recheck)
             (fn-owner-history-capture-slot fn-owner-history-read-slot
              fn-owner-canonical-epoch fn-hep-capture-livep fn-hed-read-step
              fn-hep-page-read fn-hhc-at fn-hhc-matches fn-hhc-sourcep
              fn-hhc-widthp fn-hed-at fn-hed-leafp)))))
