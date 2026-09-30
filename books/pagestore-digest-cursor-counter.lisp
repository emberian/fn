;; Proof-only reachability carry tying BLAKE3 counters to source coordinates.
(in-package "ACL2")
(include-book "pagestore-digest-byte-domain")
(local (include-book "arithmetic-5/top" :dir :system))

(defun-nx pgs-dcs-counter-framesp (depth pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix depth) :verify-guards nil))
  (if (zp depth) t
    (let ((frame (pgs-dc-framesi (- depth 1) pgs-digest-state)))
      (and (equal (fn-b3-nthx 1 frame) (* 128 (fn-b3-nthx 3 frame)))
           (pgs-dcs-counter-framesp (- depth 1) pgs-digest-state)))))

(defun-nx pgs-dcs-counterp (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (equal (pgs-dc-start pgs-digest-state) (* 128 (pgs-dc-counter pgs-digest-state)))
       (pgs-dcs-counter-framesp (pgs-dc-depth pgs-digest-state) pgs-digest-state)))

(defthm pgs-dcs-counter-framesp-of-scalar-update
  (implies (and (natp field) (not (equal field *pgs-dc-framesi*)))
           (equal (pgs-dcs-counter-framesp depth (update-nth field value pgs-digest-state))
                  (pgs-dcs-counter-framesp depth pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcs-counter-framesp depth pgs-digest-state)
                  :expand ((pgs-dcs-counter-framesp depth (update-nth field value pgs-digest-state)))
                  :in-theory (e/d (pgs-dcs-counter-framesp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx)))))

(defthm pgs-dcs-counter-framesp-of-frame-update-prefix
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (pgs-dcs-counter-framesp depth
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (pgs-dcs-counter-framesp depth pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcs-counter-framesp depth pgs-digest-state)
                  :expand ((pgs-dcs-counter-framesp depth
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state)))
                  :in-theory (e/d (pgs-dcs-counter-framesp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx)))))

(defthm pgs-dcs-counter-frames-top-unfolds
  (implies (and (posp depth) (pgs-dcs-counter-framesp depth pgs-digest-state))
           (and (equal (fn-b3-nthx 1 (pgs-dc-framesi (- depth 1) pgs-digest-state))
                       (* 128 (fn-b3-nthx 3 (pgs-dc-framesi (- depth 1) pgs-digest-state))))
                (pgs-dcs-counter-framesp (- depth 1) pgs-digest-state)))
  :hints (("Goal" :expand ((pgs-dcs-counter-framesp depth pgs-digest-state))
                  :in-theory (disable pgs-dcs-counter-framesp fn-b3-nthx))))

(defthm pgs-dcs-byte-begin-establishes-counter
  (pgs-dcs-counterp (pgs-dcb-begin sel base byte-total capture lease pgs-digest-state))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-counterp pgs-dcb-begin pgs-dc-begin)
                                   (nth update-nth pgs-dcs-counter-framesp pgs-dcb-word-count))
                  :expand ((:free (cursor) (pgs-dcs-counter-framesp 0 cursor))))))

(defthm pgs-dcs-counter-framesp-zero
  (pgs-dcs-counter-framesp 0 pgs-digest-state)
  :hints (("Goal" :in-theory (enable pgs-dcs-counter-framesp))))

(defthm pgs-dcs-counter-framesp-of-top-frame-update
  (implies (and (natp index) (equal depth (+ 1 index)))
           (equal (pgs-dcs-counter-framesp depth
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (and (equal (fn-b3-nthx 1 frame) (* 128 (fn-b3-nthx 3 frame)))
                       (pgs-dcs-counter-framesp index pgs-digest-state))))
  :hints (("Goal"
            :expand ((pgs-dcs-counter-framesp depth
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                     (:free (cursor) (pgs-dcs-counter-framesp (+ 1 index) cursor)))
            :in-theory (e/d (pgs-dc-framesi)
                             (nth update-nth pgs-dcs-counter-framesp fn-b3-nthx)))))

(defthm pgs-dcs-core-step-preserves-counter
  (implies (and (pgs-dcd-domainp limit pgs-digest-state) (pgs-dcs-counterp pgs-digest-state))
           (pgs-dcs-counterp (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use ((:instance pgs-dcs-counter-frames-top-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)))
                  (:instance pgs-dcd-top-frame-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state))))
            :expand ((:free (cursor)
                       (pgs-dcs-counter-framesp (+ 1 (nth *pgs-dc-depth* pgs-digest-state)) cursor))
                     (:free (cursor)
                       (pgs-dcs-counter-framesp (nth *pgs-dc-depth* pgs-digest-state) cursor)))
            :in-theory (e/d (pgs-dcs-counterp pgs-dcd-domainp pgs-dc-step
                                                pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcs-counter-framesp pgs-dcd-framesp pgs-dcd-powerp
                                  pgs-dcs-counter-frames-top-unfolds pgs-dcd-top-frame-unfolds
                                  fn-b3-output fn-b3-output-cv fn-b3-output-root pgs-octets-be-nat))
            :do-not-induct t)))

(defthm pgs-dcs-byte-step-preserves-counter
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state) (pgs-dcs-counterp pgs-digest-state))
           (pgs-dcs-counterp (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
  :hints (("Goal" :use pgs-dcs-core-step-preserves-counter
                  :in-theory (e/d (pgs-dbd-domainp pgs-dcs-counterp pgs-dcb-step)
                                   (nth update-nth pgs-dcd-domainp pgs-dbd-framesp
                                        pgs-dcs-counter-framesp pgs-dc-step
                                        pgs-dcs-core-step-preserves-counter fn-b3-output pgs-dc-pad-block))
                  :do-not-induct t)))

(defthm pgs-dcs-supported-counter-bound
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state) (pgs-dcs-counterp pgs-digest-state)
                (<= (pgs-dc-total pgs-digest-state) (expt 2 64)))
           (<= (pgs-dc-counter pgs-digest-state) (expt 2 57)))
  :hints (("Goal" :in-theory (e/d (pgs-dbd-domainp pgs-dcd-domainp pgs-dcs-counterp)
                                   (pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp pgs-dcd-powerp))))
  :rule-classes (:rewrite :linear))

(defthm pgs-dcs-supported-frame-counter-bound
  (implies (and (natp depth) (natp index) (< index depth)
                (natp total) (<= total (expt 2 64))
                (pgs-dcd-framesp depth limit total pgs-digest-state)
                (pgs-dcs-counter-framesp depth pgs-digest-state))
           (<= (fn-b3-nthx 3 (pgs-dc-framesi index pgs-digest-state)) (expt 2 57)))
  :hints (("Goal" :induct (pgs-dcs-counter-framesp depth pgs-digest-state)
                  :expand ((pgs-dcd-framesp depth limit total pgs-digest-state))
                  :in-theory (e/d (pgs-dcs-counter-framesp)
                                   (pgs-dcd-framesp fn-b3-nthx expt))))
  :rule-classes nil)

(in-theory (disable pgs-dcs-counterp pgs-dcs-counter-framesp))
