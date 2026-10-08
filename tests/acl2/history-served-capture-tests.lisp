; Full capture effects, wrong-root substitution, and an omitted publication write.
(in-package "ACL2")
(include-book "../../books/owner-history-capture")
(include-book "owner-history-sync-tests")

(defthm fn-hcst-positive
 (and (fn-hist-of-storep nil (fn-owner-store (fn-hhs-owner-state)))
      (and (equal (fn-hsc-complete-capture :checkpoint
                    (mv-nth 1 (fn-owner-sco-capture-served 8 100 "r3" (fn-hhs-owner-state))) nil)
                  (mv-nth 1 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state))))
           (equal (mv-nth 2 (fn-owner-sco-capture-served 8 100 "r3" (fn-hhs-owner-state)))
                  (mv-nth 2 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state)))))))

(defthm fn-hcst-wrong-root
 (and (not (fn-hist-of-storep '(phantom) (fn-owner-store (fn-hhs-owner-state))))
      (not (and
       (equal (fn-hsc-complete-capture :checkpoint
               (mv-nth 1 (fn-owner-sco-capture-served 8 100 "r3" (fn-hhs-owner-state))) '(phantom))
              (mv-nth 1 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state))))
       (equal (mv-nth 2 (fn-owner-sco-capture-served 8 100 "r3" (fn-hhs-owner-state)))
              (mv-nth 2 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state))))))))

(defthm fn-hcst-skipped-publication-write
 (and (fn-hist-of-storep nil (fn-owner-store (fn-hhs-owner-state)))
      (and (equal (fn-hsc-complete-capture :checkpoint
                    (mv-nth 1 (fn-owner-sco-capture-served 8 100 "r3" (fn-hhs-owner-state))) nil)
                  (mv-nth 1 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state))))
           (equal (mv-nth 2 (fn-owner-sco-capture-served 8 100 "r3" (fn-hhs-owner-state)))
                  (mv-nth 2 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state)))))
      (not (equal (fn-hhs-owner-state)
                  (mv-nth 2 (fn-owner-sco-capture 8 100 "r3" (fn-hhs-owner-state)))))))

(defteeth fn-owner-sco-capture-served-is-reference
 :claim (((history (fn-hist-of-storep records (fn-owner-store st))))
  (and (equal (fn-hsc-complete-capture :checkpoint
                (mv-nth 1 (fn-owner-sco-capture-served override free revision st)) records)
              (mv-nth 1 (fn-owner-sco-capture override free revision st)))
       (equal (mv-nth 2 (fn-owner-sco-capture-served override free revision st))
              (mv-nth 2 (fn-owner-sco-capture override free revision st)))))
 :subject fn-owner-sco-capture-served
 :witness ((records nil) (override 8) (free 100) (revision "r3") (st (fn-hhs-owner-state)))
 :witness-lemma fn-hcst-positive
 :breaks ((history ((records '(phantom)) (override 8) (free 100) (revision "r3")
                    (st (fn-hhs-owner-state))) :lemma fn-hcst-wrong-root))
 :mutations ((skip-publication-write
  (:conclusion (equal st (mv-nth 2 (fn-owner-sco-capture override free revision st))))
  ((records nil) (override 8) (free 100) (revision "r3") (st (fn-hhs-owner-state)))
  :fault "a capture that omits the in-flight/attempt/serial writes cannot own its publication"
  :lemma fn-hcst-skipped-publication-write)))
