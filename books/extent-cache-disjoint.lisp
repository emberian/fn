; Carried unique-charge invariant and its transition proofs.
(in-package "ACL2")
(include-book "extent-cache-token")

(defun fn-xc-token-apart-from (token i fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i))
                  :measure (nfix (- (fn-xcs-count fn-xcs) i))))
  (if (and (natp i) (< i (fn-xcs-count fn-xcs)))
      (and (not (equal token (fn-xc-slot-token i fn-xcs)))
           (fn-xc-token-apart-from token (1+ i) fn-xcs))
    t))

(defun fn-xc-token-disjoint-from (i fn-xcs)
  (declare (xargs :stobjs fn-xcs
                  :guard (and (fn-xcsp fn-xcs) (natp i))
                  :measure (nfix (- (fn-xcs-count fn-xcs) i))))
  (if (and (natp i) (< i (fn-xcs-count fn-xcs)))
      (let ((token (fn-xc-slot-token i fn-xcs)))
        (and (or (not token) (fn-xc-token-apart-from token (1+ i) fn-xcs))
             (fn-xc-token-disjoint-from (1+ i) fn-xcs)))
    t))

(defun fn-xc-token-disjointp (fn-xcs)
  (declare (xargs :stobjs fn-xcs :guard (fn-xcsp fn-xcs)))
  (fn-xc-token-disjoint-from 0 fn-xcs))

(in-theory (disable fn-xc-token-apart-from fn-xc-token-disjoint-from fn-xc-token-disjointp fn-xc-write-okp))

(defthm fn-xc-token-apart-from-member
  (implies (and (fn-xc-token-apart-from token i fn-xcs)
                (natp i) (natp j) (<= i j) (< j (fn-xcs-count fn-xcs)))
           (not (equal token (fn-xc-slot-token j fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-token-apart-from token i fn-xcs)
           :in-theory (enable fn-xc-token-apart-from))))

(defthm fn-xc-token-disjoint-from-pair
  (implies (and (fn-xc-token-disjoint-from n fn-xcs)
                (natp n) (natp i) (natp k) (<= n i) (< i k)
                (< k (fn-xcs-count fn-xcs)) (fn-xc-slot-token i fn-xcs))
           (not (equal (fn-xc-slot-token i fn-xcs) (fn-xc-slot-token k fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-xc-token-disjoint-from n fn-xcs)
           :in-theory (enable fn-xc-token-disjoint-from))
          ("Subgoal *1/1" :use (:instance fn-xc-token-apart-from-member
                                  (token (fn-xc-slot-token n fn-xcs)) (i (1+ n)) (j k)))))

(defthm fn-xc-held-token-has-one-slot
  (implies (and (fn-xc-token-disjointp slots)
                (fn-xc-holds i token slots)
                (fn-xc-holds k token slots))
           (equal i k))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-token-disjointp fn-xc-holds)
           :use ((:instance fn-xc-token-disjoint-from-pair (n 0) (fn-xcs slots))
                 (:instance fn-xc-token-disjoint-from-pair (n 0) (i k) (k i) (fn-xcs slots))))))

(defthm fn-xc-token-absent-except-tail
  (implies (and (not (fn-xc-find-token-except token target 0 fn-xcs)) token
                (natp n) (natp target) (< target n))
           (fn-xc-token-apart-from token n fn-xcs))
  :hints (("Goal" :induct (fn-xc-token-apart-from token n fn-xcs)
           :in-theory (enable fn-xc-token-apart-from))
          ("Subgoal *1/2" :use (:instance fn-xc-token-absent-except-at (j n)))
          ("Subgoal *1/1" :use (:instance fn-xc-token-absent-except-at (j n)))))

(defthm fn-xc-token-apart-from-after-write
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (natp n) (fn-xc-token-apart-from token n fn-xcs)
                (or (< i n)
                    (not (equal token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer)))))
           (fn-xc-token-apart-from token n
             (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))
  :hints (("Goal" :induct (fn-xc-token-apart-from token n fn-xcs)
           :in-theory (enable fn-xc-token-apart-from))))

(defthm fn-xc-token-disjoint-from-after-write
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (natp n) (fn-xc-token-disjoint-from n fn-xcs)
                (not (fn-xc-find-token-except
                       (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer) i 0 fn-xcs)))
           (fn-xc-token-disjoint-from n
             (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))
  :hints (("Goal" :induct (fn-xc-token-disjoint-from n fn-xcs)
           :in-theory (enable fn-xc-token-disjoint-from)
           :expand ((:free (s) (fn-xc-token-disjoint-from n s))))
          ("Subgoal *1/1" :use (:instance fn-xc-token-absent-except-at
                                 (token (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer))
                                 (target i) (j n)))))

(defthm fn-xc-write-preserves-token-disjointp
  (implies (and (fn-xc-write-okp i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)
                (fn-xc-token-disjointp fn-xcs)
                (not (fn-xc-find-token-except
                       (fn-xc-token kind tokp tid tcid file eoff elen a b c d start trailer) i 0 fn-xcs)))
           (fn-xc-token-disjointp
             (fn-xc-write i kind tokp tid tcid file eoff elen a b c d start trailer stamp fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-token-disjointp))))

(defthm fn-xc-token-apart-from-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp n))
           (equal (fn-xc-token-apart-from token n (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc)))
                  (fn-xc-token-apart-from token n fn-xcs)))
  :hints (("Goal" :induct (fn-xc-token-apart-from token n fn-xcs)
           :in-theory (enable fn-xc-token-apart-from fn-xc-touch))))

(defthm fn-xc-touch-count
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc))
           (equal (fn-xcs-count (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc))) (fn-xcs-count fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-touch))))

(defthm fn-xc-slot-token-after-touch-total
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp j))
           (equal (fn-xc-slot-token j (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc)))
                  (fn-xc-slot-token j fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-touch))))

(defthm fn-xc-token-disjoint-from-after-touch
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (natp n))
           (equal (fn-xc-token-disjoint-from n (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc)))
                  (fn-xc-token-disjoint-from n fn-xcs)))
  :hints (("Goal" :induct (fn-xc-token-disjoint-from n fn-xcs)
           :in-theory (enable fn-xc-token-disjoint-from)
           :expand ((:free (s) (fn-xc-token-disjoint-from n s))))))

(defthm fn-xc-touch-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-token-disjointp))))

(defthm fn-xc-free-count
  (implies (and (fn-xcsp fn-xcs) (natp i))
           (equal (fn-xcs-count (mv-nth 2 (fn-xc-free i fn-xcs))) (fn-xcs-count fn-xcs)))
  :hints (("Goal" :in-theory (enable fn-xc-free))))

(defthm fn-xc-slot-token-after-free
  (implies (and (fn-xcsp fn-xcs) (natp i) (natp j) (< j (fn-xcs-count fn-xcs)))
           (equal (fn-xc-slot-token j (mv-nth 2 (fn-xc-free i fn-xcs)))
                  (if (equal j i) nil (fn-xc-slot-token j fn-xcs))))
  :hints (("Goal" :in-theory (enable fn-xc-free fn-xc-slot-token fn-xc-token fn-xcs-set-kind-is-update-nth
                    fn-xcs-get-kind-is-nth fn-xcs-get-tokp-is-nth fn-xcs-get-tid-is-nth fn-xcs-get-tcid-is-nth fn-xcs-get-file-is-nth fn-xcs-get-eoff-is-nth fn-xcs-get-elen-is-nth fn-xcs-get-a-is-nth fn-xcs-get-b-is-nth fn-xcs-get-c-is-nth fn-xcs-get-d-is-nth fn-xcs-get-start-is-nth fn-xcs-get-trailer-is-nth))))

(in-theory (disable fn-xc-free fn-xc-yield))

(defthm fn-xc-token-apart-from-after-free
  (implies (and (fn-xcsp fn-xcs) (natp i) (natp n) token
                (fn-xc-token-apart-from token n fn-xcs))
           (fn-xc-token-apart-from token n (mv-nth 2 (fn-xc-free i fn-xcs))))
  :hints (("Goal" :induct (fn-xc-token-apart-from token n fn-xcs)
           :in-theory (enable fn-xc-token-apart-from))))

(defthm fn-xc-token-disjoint-from-after-free
  (implies (and (fn-xcsp fn-xcs) (natp i) (natp n) (fn-xc-token-disjoint-from n fn-xcs))
           (fn-xc-token-disjoint-from n (mv-nth 2 (fn-xc-free i fn-xcs))))
  :hints (("Goal" :induct (fn-xc-token-disjoint-from n fn-xcs)
           :in-theory (enable fn-xc-token-disjoint-from)
           :expand ((fn-xc-token-disjoint-from n (mv-nth 2 (fn-xc-free i fn-xcs)))))))

(defthm fn-xc-free-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (natp i) (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp (mv-nth 2 (fn-xc-free i fn-xcs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-token-disjointp))))

(defthm fn-xc-yield-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp (mv-nth 3 (fn-xc-yield fn-xcs fn-xcc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-yield)
           :use (:instance fn-xc-free-preserves-token-disjointp
                            (i (or (fn-xc-lru (fn-xc-lo 1 fn-xcc) (fn-xc-hi 1 fn-xcc) nil fn-xcs)
                                   (fn-xc-lru (fn-xc-lo 2 fn-xcc) (fn-xc-hi 2 fn-xcc) nil fn-xcs)))))))

(defthm fn-xc-install-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc) (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp
             (mv-nth 3 (fn-xc-install kind tokp tid tcid file eoff elen a b c d start trailer fn-xcs fn-xcc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-xc-install fn-xc-install-conflict fn-xc-write-okp)
           :use ((:instance fn-xc-touch-preserves-token-disjointp
                            (i (fn-xc-find (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) t
                                           kind file eoff elen a b c d trailer start fn-xcs)))
                 (:instance fn-xc-write-preserves-token-disjointp
                            (i (or (fn-xc-find-free (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) fn-xcs)
                                   (fn-xc-lru (fn-xc-lo kind fn-xcc) (fn-xc-hi kind fn-xcc) nil fn-xcs)))
                            (stamp (fn-xc-tick fn-xcc)))))))

