;; Proof-only representation domain. No predicate here runs on the served path.
(in-package "ACL2")
(include-book "pagestore-digest-cursor")
(local (include-book "arithmetic-5/top" :dir :system))

(defun-sk pgs-dcd-powerp (power limit)
  (exists (exponent)
    (and (natp exponent) (<= exponent limit)
         (equal power (expt 2 exponent)))))

(defthm pgs-dcd-powerp-one
  (implies (natp limit) (pgs-dcd-powerp 1 limit))
  :hints (("Goal" :use ((:instance pgs-dcd-powerp-suff (power 1) (exponent 0)))
                  :in-theory (disable pgs-dcd-powerp))))

(defthm pgs-dcd-powerp-bound
  (implies (and (natp limit) (pgs-dcd-powerp power limit))
           (and (posp power) (<= power (expt 2 limit))))
  :hints (("Goal" :in-theory (enable pgs-dcd-powerp)))
  :rule-classes (:rewrite
                 (:linear :corollary
                   (implies (and (natp limit) (pgs-dcd-powerp power limit))
                            (<= power (expt 2 limit))))))

(defthm pgs-dcd-powerp-double-under-bound
  (implies (and (natp limit) (pgs-dcd-powerp power limit)
                (< (* 2 power) (expt 2 (+ 1 limit))))
           (pgs-dcd-powerp (* 2 power) limit))
  :hints (("Goal"
            :use ((:instance pgs-dcd-powerp-suff
                    (power (* 2 power))
                    (exponent (+ 1 (pgs-dcd-powerp-witness power limit)))))
            :in-theory (enable pgs-dcd-powerp))))

(defthm pgs-dcd-search-doubling-stays-in-domain
  (implies (and (natp limit) (pgs-dcd-powerp power limit)
                (natp nwords) (< (* 256 power) nwords)
                (<= nwords (* 128 (expt 2 (+ 1 limit)))))
           (pgs-dcd-powerp (* 2 power) limit))
  :hints (("Goal" :use (pgs-dcd-powerp-bound pgs-dcd-powerp-double-under-bound)
                  :in-theory (disable pgs-dcd-powerp pgs-dcd-powerp-bound
                                      pgs-dcd-powerp-double-under-bound))))

(defun-nx pgs-dcd-framesp (depth limit total pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix depth) :verify-guards nil))
  (if (zp depth) t
    (let* ((index (- depth 1))
           (frame (pgs-dc-framesi index pgs-digest-state))
           (start (fn-b3-nthx 1 frame)) (end (fn-b3-nthx 2 frame)))
      (and (member-eq (fn-b3-nthx 0 frame) '(:left :right))
           (natp start) (natp end) (<= start end) (<= end total)
           (natp (fn-b3-nthx 3 frame))
           (<= (- end start) (* 128 (expt 2 (- (- limit index) 1))))
           (implies (equal (fn-b3-nthx 0 frame) :right)
                    (and (true-listp (fn-b3-nthx 4 frame))
                         (equal (len (fn-b3-nthx 4 frame)) 8)))
           (pgs-dcd-framesp index limit total pgs-digest-state)))))

(defun-nx pgs-dcd-domainp (limit pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (natp limit) (<= limit 63)
       (natp (pgs-dc-depth pgs-digest-state)) (<= (pgs-dc-depth pgs-digest-state) limit)
       (natp (pgs-dc-total pgs-digest-state)) (natp (pgs-dc-start pgs-digest-state))
       (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
       (natp (pgs-dc-counter pgs-digest-state))
       (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
       (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
       (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
       (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))
           (* 128 (expt 2 (- limit (pgs-dc-depth pgs-digest-state)))))
       (true-listp (pgs-dc-cv pgs-digest-state)) (equal (len (pgs-dc-cv pgs-digest-state)) 8)
       (member-eq (pgs-dc-mode pgs-digest-state) '(:node :split :chunk :return :root :done))
       (implies (member-eq (pgs-dc-mode pgs-digest-state) '(:node :split))
                (equal (pgs-dc-pos pgs-digest-state) (pgs-dc-start pgs-digest-state)))
       (implies (equal (pgs-dc-mode pgs-digest-state) :split)
                (and (< (pgs-dc-depth pgs-digest-state) limit)
                     (pgs-dcd-powerp (pgs-dc-power pgs-digest-state)
                                     (- (- limit (pgs-dc-depth pgs-digest-state)) 1))
                     (< (* 128 (pgs-dc-power pgs-digest-state))
                        (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
       (pgs-dcd-framesp (pgs-dc-depth pgs-digest-state) limit
                        (pgs-dc-total pgs-digest-state) pgs-digest-state)))

(defthm pgs-dcd-framesp-of-scalar-update
  (implies (and (natp field) (not (equal field *pgs-dc-framesi*)))
           (equal (pgs-dcd-framesp depth limit total (update-nth field value pgs-digest-state))
                  (pgs-dcd-framesp depth limit total pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcd-framesp depth limit total pgs-digest-state)
                  :expand ((pgs-dcd-framesp depth limit total (update-nth field value pgs-digest-state)))
                  :in-theory (e/d (pgs-dcd-framesp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx expt)))))

(defthm pgs-dcd-framesp-of-frame-update-prefix
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (pgs-dcd-framesp depth limit total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (pgs-dcd-framesp depth limit total pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcd-framesp depth limit total pgs-digest-state)
                  :expand ((pgs-dcd-framesp depth limit total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state)))
                  :in-theory (e/d (pgs-dcd-framesp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx expt)))))

(defthm pgs-dcd-begin-establishes-domain
  (implies (and (natp limit) (<= limit 63) (natp nb)
                (<= (* 8 nb) (* 128 (expt 2 limit))))
           (pgs-dcd-domainp limit (pgs-dc-begin sel base nb capture lease pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcd-domainp pgs-dc-begin)
                                   (nth update-nth pgs-dcd-framesp))
                  :expand ((:free (limit total cursor) (pgs-dcd-framesp 0 limit total cursor))))))

(defthm pgs-dcd-domain-implies-step-guard
  (implies (pgs-dcd-domainp limit pgs-digest-state)
           (and (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp))))

(defthm pgs-dcd-nonleaf-has-depth-room
  (implies (and (natp limit) (natp depth) (<= depth limit)
                (< 128 nwords) (<= nwords (* 128 (expt 2 (- limit depth)))))
           (< depth limit))
  :hints (("Goal" :cases ((equal depth limit)) :in-theory (disable expt))))

(defthm pgs-dcd-node-step-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :node))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal" :use ((:instance pgs-dcd-nonleaf-has-depth-room
                           (depth (pgs-dc-depth pgs-digest-state))
                           (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
                  :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                                   (nth update-nth pgs-dcd-framesp pgs-dcd-powerp pgs-dcd-nonleaf-has-depth-room))
                  :do-not-induct t)))

(defthm pgs-dcd-split-search-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :split)
                (< (* 256 (pgs-dc-power pgs-digest-state))
                   (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use ((:instance pgs-dcd-powerp-bound
                    (power (pgs-dc-power pgs-digest-state))
                    (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1)))
                  (:instance pgs-dcd-search-doubling-stays-in-domain
                    (power (pgs-dc-power pgs-digest-state))
                    (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))
                    (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1))))
            :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                             (nth update-nth pgs-dcd-framesp pgs-dcd-powerp
                                  pgs-dcd-powerp-bound pgs-dcd-search-doubling-stays-in-domain))
            :do-not-induct t)))

(defthm pgs-dcd-both-child-spans-fit
  (implies (and (rationalp power) (rationalp capacity) (rationalp nwords)
                (<= power capacity) (<= nwords (* 256 power)))
           (and (<= (* 128 power) (* 128 capacity))
                (<= (- nwords (* 128 power)) (* 128 capacity)))))

(defthm pgs-dcd-split-push-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :split)
                (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))
                    (* 256 (pgs-dc-power pgs-digest-state))))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use ((:instance pgs-dcd-powerp-bound
                    (power (pgs-dc-power pgs-digest-state))
                    (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1)))
                  (:instance pgs-dcd-both-child-spans-fit
                    (power (pgs-dc-power pgs-digest-state))
                    (capacity (expt 2 (- (- limit (pgs-dc-depth pgs-digest-state)) 1)))
                    (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
            :expand ((:free (bound total cursor)
                       (pgs-dcd-framesp (+ 1 (nth *pgs-dc-depth* pgs-digest-state)) bound total cursor)))
            :in-theory (e/d (pgs-dcd-domainp pgs-dc-step pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcd-framesp pgs-dcd-powerp pgs-dcd-powerp-bound pgs-dcd-both-child-spans-fit))
            :do-not-induct t)))

(defthm pgs-dcd-chunk-step-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :chunk))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal" :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                                   (nth update-nth pgs-dcd-framesp pgs-dcd-powerp fn-b3-output
                                        fn-b3-output-cv pgs-dc-pad-block))
                  :do-not-induct t)))

(defthm pgs-dcd-root-done-step-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (member-eq (pgs-dc-mode pgs-digest-state) '(:root :done)))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal" :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                                   (nth update-nth pgs-dcd-framesp pgs-dcd-powerp fn-b3-output-root
                                        pgs-octets-be-nat))
                  :do-not-induct t)))

(defthm pgs-dcd-return-empty-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :return)
                (equal (pgs-dc-depth pgs-digest-state) 0))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal" :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                                   (nth update-nth pgs-dcd-framesp pgs-dcd-powerp))
                  :do-not-induct t)))

(defthm pgs-dcd-top-frame-unfolds
  (implies (and (posp depth) (pgs-dcd-framesp depth limit total pgs-digest-state))
           (let* ((index (- depth 1)) (frame (pgs-dc-framesi index pgs-digest-state))
                  (start (fn-b3-nthx 1 frame)) (end (fn-b3-nthx 2 frame)))
             (and (member-eq (fn-b3-nthx 0 frame) '(:left :right))
                  (natp start) (natp end) (<= start end) (<= end total)
                  (natp (fn-b3-nthx 3 frame))
                  (<= (- end start) (* 128 (expt 2 (- (- limit index) 1))))
                  (implies (equal (fn-b3-nthx 0 frame) :right)
                           (and (true-listp (fn-b3-nthx 4 frame))
                                (equal (len (fn-b3-nthx 4 frame)) 8)))
                  (pgs-dcd-framesp index limit total pgs-digest-state))))
  :hints (("Goal" :expand ((pgs-dcd-framesp depth limit total pgs-digest-state))
                  :in-theory (disable pgs-dcd-framesp fn-b3-nthx expt))))

(defthm pgs-dcd-parent-capacity-is-larger
  (implies (integerp level)
           (<= (* 128 (expt 2 level)) (* 128 (expt 2 (+ 1 level))))))

(defthm pgs-dcd-parent-expt-capacity-linear
  (implies (integerp level)
           (<= (expt 2 (+ 7 level)) (expt 2 (+ 8 level))))
  :rule-classes :linear)

(defthm pgs-dcd-return-right-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :return)
                (posp (pgs-dc-depth pgs-digest-state))
                (not (equal (fn-b3-nthx 0 (pgs-dc-framesi
                                (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)) :left)))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use ((:instance pgs-dcd-top-frame-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state)))
                  (:instance pgs-dcd-parent-capacity-is-larger
                    (level (- limit (pgs-dc-depth pgs-digest-state)))))
            :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                             (nth update-nth pgs-dcd-framesp pgs-dcd-powerp fn-b3-output
                                  fn-b3-output-cv fn-b3-cv8 pgs-dcd-top-frame-unfolds
                                  pgs-dcd-parent-capacity-is-larger
                                  EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1
                                  |(< (expt x n) (expt x m))|))
            :do-not-induct t)))

(defthm pgs-dcd-return-left-preserves-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :return)
                (posp (pgs-dc-depth pgs-digest-state))
                (equal (fn-b3-nthx 0 (pgs-dc-framesi
                                (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)) :left))
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use ((:instance pgs-dcd-top-frame-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state))))
            :expand ((:free (bound total cursor)
                       (pgs-dcd-framesp (nth *pgs-dc-depth* pgs-digest-state) bound total cursor)))
            :in-theory (e/d (pgs-dcd-domainp pgs-dc-step pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcd-framesp pgs-dcd-powerp fn-b3-output
                                  fn-b3-output-cv pgs-dcd-top-frame-unfolds))
            :do-not-induct t)))

(defthm pgs-dcd-domain-modes
  (implies (pgs-dcd-domainp limit pgs-digest-state)
           (and (natp (pgs-dc-depth pgs-digest-state))
                (member-eq (pgs-dc-mode pgs-digest-state) '(:node :split :chunk :return :root :done))))
  :hints (("Goal" :in-theory (enable pgs-dcd-domainp))))

(defthm pgs-dcd-step-preserves-domain
  (implies (pgs-dcd-domainp limit pgs-digest-state)
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use (pgs-dcd-domain-modes pgs-dcd-node-step-preserves-domain
                  pgs-dcd-split-search-preserves-domain pgs-dcd-split-push-preserves-domain
                  pgs-dcd-chunk-step-preserves-domain pgs-dcd-root-done-step-preserves-domain
                  pgs-dcd-return-empty-preserves-domain pgs-dcd-return-right-preserves-domain
                  pgs-dcd-return-left-preserves-domain)
            :in-theory (disable pgs-dcd-domainp pgs-dc-step pgs-dcd-framesp pgs-dcd-powerp
                                pgs-dcd-domain-modes pgs-dcd-node-step-preserves-domain
                                pgs-dcd-split-search-preserves-domain pgs-dcd-split-push-preserves-domain
                                pgs-dcd-chunk-step-preserves-domain pgs-dcd-root-done-step-preserves-domain
                                pgs-dcd-return-empty-preserves-domain pgs-dcd-return-right-preserves-domain
                                pgs-dcd-return-left-preserves-domain))))

(defthm pgs-dcd-step-is-never-invalid
  (implies (pgs-dcd-domainp limit pgs-digest-state)
           (member-eq (mv-nth 0 (pgs-dc-step block pgs-digest-state)) '(:continue :done)))
  :hints (("Goal"
            :use ((:instance pgs-dcd-powerp-bound
                    (power (pgs-dc-power pgs-digest-state))
                    (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1))))
            :in-theory (e/d (pgs-dcd-domainp pgs-dc-step)
                             (nth update-nth pgs-dcd-framesp pgs-dcd-powerp pgs-dcd-powerp-bound
                                  fn-b3-output fn-b3-output-cv fn-b3-output-root pgs-octets-be-nat)))))

(defthm pgs-dcd-u64-word-profile-fits
  (implies (and (natp nb) (<= (* 8 nb) (expt 2 64)))
           (pgs-dcd-domainp 57 (pgs-dc-begin sel base nb capture lease pgs-digest-state)))
  :hints (("Goal" :use ((:instance pgs-dcd-begin-establishes-domain (limit 57)))
                  :in-theory (disable pgs-dcd-domainp pgs-dc-begin pgs-dcd-begin-establishes-domain))))

(defthm pgs-dcd-u32-directory-profile-fits
  (implies (and (natp page-count) (<= page-count (expt 2 32)))
           (pgs-dcd-domainp 36
             (pgs-dc-begin sel base (* 256 page-count) capture lease pgs-digest-state)))
  :hints (("Goal" :use ((:instance pgs-dcd-begin-establishes-domain
                            (limit 36) (nb (* 256 page-count))))
                  :in-theory (disable pgs-dcd-domainp pgs-dc-begin pgs-dcd-begin-establishes-domain))))

(in-theory (disable pgs-dcd-powerp pgs-dcd-framesp pgs-dcd-domainp))
