; The table's token projection and the funded backing install commute.
(in-package "ACL2")
(include-book "extent-cache-memory-proof")

(defthm fn-xc-keyp-has-kind
  (implies (fn-xc-keyp kind file eoff elen a b c d start trailer)
           (member-equal kind '(1 2 3)))
  :hints (("Goal" :in-theory (enable fn-xc-keyp))))

(defthm fn-xc-list-six
  (implies (and (true-listp x) (equal (len x) 6))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)) x))
  :hints (("Goal" :do-not-induct t :use fn-xc-take-len
           :in-theory (e/d (take nth) (fn-xc-take-len))
           :expand ((take 6 x) (take 5 (cdr x)) (take 4 (cddr x))
                    (take 3 (cdddr x)) (take 2 (cddddr x)) (take 1 (cdr (cddddr x)))))))

(defthm fn-xc-install-row-projections
  (let* ((r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (new (mv-nth 3 r))
         (writes (and (member-equal (mv-nth 0 r) '(:installed :replaced)) (equal i (mv-nth 1 r)))))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (natp i))
             (and (equal (fn-xcs-count new) (fn-xcs-count slots))
                  (equal (fn-xcs-get-kind i new) (if writes kind (fn-xcs-get-kind i slots)))
                  (equal (fn-xc-slot-token i new)
                         (if writes (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer)
                           (fn-xc-slot-token i slots))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install fn-xc-touch fn-xc-write-okp)
                                (fn-xc-write fn-xc-token fn-xc-slot-token fn-xc-keyp unsigned-byte-p))
           :use ((:instance fn-xc-keyp-has-kind)
                 (:instance fn-xc-next-stamp-results (fn-xcc cells))))))

(defthm fn-xc-entry-install-row-projections
  (let* ((r (fn-xc-install-entry file eoff elen trailer token slots cells))
         (new (mv-nth 3 r))
         (writes (and (member-equal (mv-nth 0 r) '(:installed :replaced)) (equal i (mv-nth 1 r)))))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (natp i))
             (and (equal (fn-xcs-count new) (fn-xcs-count slots))
                  (equal (fn-xcs-get-kind i new) (if writes 1 (fn-xcs-get-kind i slots)))
                  (equal (fn-xc-slot-token i new) (if writes token (fn-xc-slot-token i slots))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xc-install-entry fn-xc-token)
                                (fn-xc-install fn-xc-slot-token))
           :use ((:instance fn-xc-list-six (x token))
                 (:instance fn-xc-install-row-projections (kind 1) (tokp nil) (tid 0) (tcid 0) (a 0) (b 0) (c 0) (d 0) (start 0))
                 (:instance fn-xc-install-row-projections (kind 1) (tokp t) (tid (nth 0 token)) (tcid (nth 1 token)) (a 0) (b 0) (c 0) (d 0) (start 0))))))

(defthm fn-xc-install-entry-funded-preserves-row-funding
  (let ((r (fn-xc-install-entry-funded ledger file eoff elen trailer token slots cells entries stage)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (natp i)
                  (< i (fn-xce-keys-length entries))
                  (fn-xce-row-fundedp i ledger slots entries))
             (fn-xce-row-fundedp i ledger (mv-nth 3 r) (mv-nth 5 r))))
  :hints (("Goal" :in-theory (e/d (fn-xc-install-entry-funded fn-xc-install-entry-bytes fn-xce-adopt fn-xce-row-fundedp)
                                (fn-xc-install-entry fn-xc-slot-token fn-xce-cached-charge))
           :use (fn-xc-entry-install-row-projections fn-xc-entry-success-placement))))

(defthm fn-xc-install-entry-funded-preserves-funded-through
  (let ((r (fn-xc-install-entry-funded ledger file eoff elen trailer token slots cells entries stage)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (natp n)
                  (<= n (fn-xce-keys-length entries))
                  (fn-xce-funded-through n ledger slots entries))
             (fn-xce-funded-through n ledger (mv-nth 3 r) (mv-nth 5 r))))
  :hints (("Goal" :induct (fn-xce-funded-through n ledger slots entries)
           :in-theory (disable fn-xc-install-entry-funded fn-xce-row-fundedp))))

(defthm fn-xc-install-entry-funded-preserves-funding
  (let ((r (fn-xc-install-entry-funded ledger file eoff elen trailer token slots cells entries stage)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xce-fundedp ledger slots entries))
             (fn-xce-fundedp ledger (mv-nth 3 r) (mv-nth 5 r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-xce-fundedp) (fn-xc-install-entry-funded fn-xce-funded-through)))))
