; Proof-only association between the real generic parser infos and the bounded
; mapper. Missing pair infos refuse; provenance never supplies absent children.
(in-package "ACL2")
(include-book "store-tree-size-info")
(include-book "consumer-checkpoint-carry-map-model")

(defun fn-ccma-coveredp (kind value info)
 (declare (xargs :guard t :verify-guards nil :measure (acl2-count value)))
 (and (fn-scs-carryp (fn-cp-nth 0 info))
  (if (not (consp value)) (null value)
   (and (fn-ccm-pair-infop info)
    (if (eq kind :list)
        (fn-ccma-coveredp :list (cdr value) (fn-ccm-info-tail info))
      (let ((entry (car value)) (ei (fn-cp-nth 1 info)))
       (and (consp entry) (fn-ccm-pair-infop ei)
            (implies (characterp (car entry))
                     (fn-ccma-coveredp :trie (cdr entry) (fn-ccm-info-tail ei)))
            (fn-ccma-coveredp :trie (cdr value) (fn-ccm-info-tail info)))))))))

(local (defthm fn-ccma-valid-root-is-actual-size
 (implies (and (fn-scsr-info-provenancep info x)
               (fn-scs-carryp (car info)))
          (equal (car info) (fn-scs-summary x)))
 :hints (("Goal" :expand ((fn-scsr-info-provenancep info x))
          :in-theory (enable fn-scsr-info-root fn-cp-nth)))))

(local (defthm fn-ccma-pair-children-have-provenance
 (implies (and (fn-scsr-info-provenancep info x) (fn-ccm-pair-infop info))
  (and (consp info) (consp (cadr info)) (consp (cddr info))
       (fn-scsr-info-provenancep (cadr info) (car x))
       (fn-scsr-info-provenancep (cddr info) (cdr x))
       (equal (car info) (fn-scs-summary x))
       (equal (car (cadr info)) (fn-scs-summary (car x)))
       (equal (car (cddr info)) (fn-scs-summary (cdr x)))))
 :hints (("Goal" :do-not-induct t
  :expand ((fn-scsr-info-provenancep info x))
  :in-theory (e/d (fn-ccm-pair-infop fn-cp-nth fn-ccm-info-tail
                    fn-scsr-info-root fn-scsr-car fn-scsr-cdr fn-scs-carryp)
                   (fn-scsr-info-provenancep fn-scs-summary))))))

(local (defthm fn-ccma-tail-is-cddr
 (equal (fn-ccm-info-tail x) (cddr x))
 :hints (("Goal" :in-theory (enable fn-ccm-info-tail nthcdr)))))
(local (defthm fn-ccma-field-one-is-cadr
 (equal (fn-cp-nth 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable fn-cp-nth)))))

(defthm fn-ccma-actual-list-target-is-complete-annotation
 (implies (and (fn-scsr-info-provenancep info rows)
               (fn-ccma-coveredp :list rows info))
          (equal (fn-ccmm-target :list rows info)
                 (fn-caam-list-annotation rows)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-ccmm-target :list rows info)
  :in-theory (e/d (fn-ccmm-target fn-ccma-coveredp fn-caam-list-annotation fn-cp-nth fn-ccm-info-tail nthcdr)
                   (fn-scs-summary fn-scs-carryp fn-scsr-info-provenancep
                    fn-ccm-pair-infop)))))

(local (defthm fn-ccma-entry-child-has-provenance
 (implies (and (fn-scsr-info-provenancep info x)
               (fn-ccm-pair-infop info) (fn-ccm-pair-infop (cadr info)))
  (and (consp (cddr (cadr info)))
       (fn-scsr-info-provenancep (cddr (cadr info)) (cdr (car x)))
       (equal (car (cddr (cadr info))) (fn-scs-summary (cdr (car x))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ccma-pair-children-have-provenance)
        (:instance fn-ccma-pair-children-have-provenance (info (cadr info)) (x (car x))))
  :in-theory (disable fn-scsr-info-provenancep fn-ccm-pair-infop
                     fn-scs-summary fn-ccma-pair-children-have-provenance)))))

(defthm fn-ccma-actual-trie-target-is-complete-annotation
 (implies (and (fn-scsr-info-provenancep info trie)
               (fn-ccma-coveredp :trie trie info))
          (equal (fn-ccmm-target :trie trie info)
                 (fn-cait-annotation trie)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-ccmm-target :trie trie info)
  :in-theory (e/d (fn-ccmm-target fn-ccma-coveredp fn-cait-annotation fn-ag-car fn-ag-cdr fn-cp-nth fn-ccm-info-tail nthcdr)
                   (fn-scs-summary fn-scs-carryp fn-scsr-info-provenancep
                    fn-ccm-pair-infop)))))
