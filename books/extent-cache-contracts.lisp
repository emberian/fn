; Full-strength original contracts that also hold on :duplicate.
; The accepted narrowed forms remain unchanged in extent-cache.
(in-package "ACL2")
(include-book "extent-cache-token")

(defthm fn-xc-install-occupancy-full-strength
(implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
        (fn-xc-install-okp kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)
        (not (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
                    :refused)))
           (let ((n0 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs))
                 (n1 (fn-xc-live-count (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))))
             (and (equal n1 (if (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :installed) (+ 1 n0) n0))
                  (<= n1 (- (fn-xc-hi kind fn-xcc) (fn-xc-lo kind fn-xcc))))))
 :rule-classes nil
 :hints (("Goal" :cases ((equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate))
                 :use (fn-xc-install-occupancy
                       (:instance fn-xc-install-duplicate-is-already-held (slots fn-xcs) (cells fn-xcc))
                       (:instance fn-xc-occupancy-bounded (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc))))
                 :in-theory (e/d (fn-xc-install-okp) (fn-xc-install-occupancy fn-xc-install-duplicate-iff-conflict fn-xc-holds fn-xc-keyp fn-xc-occupancy-bounded)))))

(defthm fn-xc-install-then-lookup-hits-present-full-strength
(implies (and (fn-xc-case-hyps)
                (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d
                            trailer start fn-xcs))
           (fn-xc-lookup-after-install))
 :rule-classes nil
 :hints (("Goal" :cases ((equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate))
                 :use (fn-xc-install-then-lookup-hits-present
                       (:instance fn-xc-install-duplicate-is-already-held (slots fn-xcs) (cells fn-xcc))
                       (:instance fn-xc-find-complete (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)) (exactp nil) (pos start)
                         (j (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t kind file eoff elen a b c d trailer start fn-xcs)))
                       (:instance fn-xc-find-bounds (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)) (exactp t) (pos start))
                       (:instance fn-xc-find-matches (i (fn-xc-lo kind fn-xcc)) (hi (fn-xc-hi kind fn-xcc)) (exactp t) (pos start)))
                 :in-theory (e/d (fn-xc-install-okp fn-xc-install-conflict fn-xc-slot-matchp fn-xc-keyp) (fn-xc-install-then-lookup-hits-present fn-xc-install-duplicate-iff-conflict fn-xc-holds)))))
