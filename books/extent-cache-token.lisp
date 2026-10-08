; Charge-token projection and duplicate admission evidence.
(in-package "ACL2")
(include-book "extent-cache")
(in-theory (disable fn-xc-token fn-xc-slot-token))

(defthm fn-xc-find-token-except-sound
  (implies (fn-xc-find-token-except token target i fn-xcs)
           (let ((j (fn-xc-find-token-except token target i fn-xcs)))
             (and token (natp j) (<= (nfix i) j) (< j (fn-xcs-count fn-xcs))
                  (not (equal j target)) (fn-xc-holds j token fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-find-token-except token target i fn-xcs)
           :in-theory (enable fn-xc-find-token-except fn-xc-holds))))

(defthm fn-xc-find-token-except-complete
  (implies (and (natp i) (natp j) (<= i j) (< j (fn-xcs-count fn-xcs))
                token (not (equal j target)) (equal token (fn-xc-slot-token j fn-xcs)))
           (fn-xc-find-token-except token target i fn-xcs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-find-token-except token target i fn-xcs)
           :in-theory (enable fn-xc-find-token-except))))

(defthm fn-xc-slot-token-after-write
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (natp j))
           (equal (fn-xc-slot-token j (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs))
                  (if (equal j i)
                      (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer)
                    (fn-xc-slot-token j fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-slot-token))))

(defthm fn-xc-install-duplicate-iff-conflict
  (iff (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)
       (mv-nth 1 (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)))
  :hints (("Goal" :in-theory (enable fn-xc-install))))

(defthm fn-xc-install-duplicate-is-already-held
  (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer slots cells))
         (target (mv-nth 0 choice)) (holder (mv-nth 1 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
         (r (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer slots cells)))
    (and (iff (equal (mv-nth 0 r) :duplicate)
              (and token (fn-xc-holds holder token slots) (not (equal holder target))))
         (implies (equal (mv-nth 0 r) :duplicate)
                  (and (equal (mv-nth 1 r) target) (equal (mv-nth 2 r) nil)
                       (equal (mv-nth 3 r) slots) (equal (mv-nth 4 r) cells)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-conflict fn-xc-holds)
           :use (:instance fn-xc-find-token-except-sound (fn-xcs slots)
                            (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
                            (i 0)
                            (target (or (fn-xc-find (fn-xc-lo kind cells) (fn-xc-hi kind cells) t
                                                   kind file eoff elen a b c d trailer start slots)
                                        (fn-xc-find-free (fn-xc-lo kind cells) (fn-xc-hi kind cells) slots)
                                        (fn-xc-lru (fn-xc-lo kind cells) (fn-xc-hi kind cells) nil slots)))))))

(defthm fn-xc-install-duplicate-for-every-other-holder
  (let* ((choice (fn-xc-install-conflict kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))
         (target (mv-nth 0 choice))
         (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer)))
    (implies (and (natp target) (fn-xc-holds j token fn-xcs) (not (equal j target)))
             (equal (mv-nth 0 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc)) :duplicate)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-install-conflict fn-xc-holds)
           :use (:instance fn-xc-find-token-except-complete
                            (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
                            (i 0)
                            (target (or (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t
                                                   kind file eoff elen a b c d trailer start fn-xcs)
                                        (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)
                                        (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs)))))))

(in-theory (disable fn-xc-write-okp))

(defthm fn-xc-write-okp-slot
  (implies (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
           (and (natp i) (< i (fn-xcs-count fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-write-okp))))

(defthm fn-xc-token-absent-except-at
  (implies (and (not (fn-xc-find-token-except token target 0 fn-xcs)) token
                (natp j) (< j (fn-xcs-count fn-xcs)) (not (equal j target)))
           (not (equal token (fn-xc-slot-token j fn-xcs))))
  :hints (("Goal" :use (:instance fn-xc-find-token-except-complete (i 0)))))

