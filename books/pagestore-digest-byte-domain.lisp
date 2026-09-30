;; Proof-only exact-byte guard carry, layered on the page representation domain.
(in-package "ACL2")
(include-book "pagestore-digest-cursor-domain")
(include-book "pagestore-digest-byte-cursor")
(local (include-book "arithmetic-5/top" :dir :system))

(defun-nx pgs-dbd-framesp (depth total pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix depth) :verify-guards nil))
  (if (zp depth) t
    (and (< (fn-b3-nthx 1 (pgs-dc-framesi (- depth 1) pgs-digest-state)) total)
         (pgs-dbd-framesp (- depth 1) total pgs-digest-state))))

(defun-nx pgs-dbd-domainp (limit byte-total pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (and (pgs-dcd-domainp limit pgs-digest-state)
       (natp byte-total)
       (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count byte-total))
       (<= (* 8 (pgs-dc-pos pgs-digest-state)) byte-total)
       (pgs-dbd-framesp (pgs-dc-depth pgs-digest-state)
                       (pgs-dc-total pgs-digest-state) pgs-digest-state)))

(defthm pgs-dbd-word-before-end-is-byte-backed
  (implies (and (natp byte-total) (natp word-offset)
                (< word-offset (pgs-dcb-word-count byte-total)))
           (<= (* 8 word-offset) byte-total))
  :hints (("Goal" :in-theory (enable pgs-dcb-word-count))))

(defthm pgs-dbd-framesp-of-scalar-update
  (implies (and (natp field) (not (equal field *pgs-dc-framesi*)))
           (equal (pgs-dbd-framesp depth total (update-nth field value pgs-digest-state))
                  (pgs-dbd-framesp depth total pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dbd-framesp depth total pgs-digest-state)
                  :expand ((pgs-dbd-framesp depth total (update-nth field value pgs-digest-state)))
                  :in-theory (e/d (pgs-dbd-framesp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx)))))

(defthm pgs-dbd-framesp-of-frame-update-prefix
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (pgs-dbd-framesp depth total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (pgs-dbd-framesp depth total pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dbd-framesp depth total pgs-digest-state)
                  :expand ((pgs-dbd-framesp depth total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state)))
                  :in-theory (e/d (pgs-dbd-framesp pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx)))))

(defthm pgs-dbd-top-frame-unfolds
  (implies (and (posp depth) (pgs-dbd-framesp depth total pgs-digest-state))
           (and (< (fn-b3-nthx 1 (pgs-dc-framesi (- depth 1) pgs-digest-state)) total)
                (pgs-dbd-framesp (- depth 1) total pgs-digest-state)))
  :hints (("Goal" :expand ((pgs-dbd-framesp depth total pgs-digest-state))
                  :in-theory (disable pgs-dbd-framesp fn-b3-nthx))))

(defthm pgs-dbd-begin-establishes-domain
  (implies (and (natp limit) (<= limit 63) (natp byte-total)
                (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit))))
           (pgs-dbd-domainp limit byte-total
             (pgs-dcb-begin sel base byte-total capture lease pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dbd-domainp pgs-dcd-domainp pgs-dcb-begin pgs-dc-begin
                                                  pgs-dcb-word-count)
                                   (nth update-nth pgs-dbd-framesp pgs-dcd-framesp))
                  :expand ((:free (limit total cursor) (pgs-dcd-framesp 0 limit total cursor))
                           (:free (total cursor) (pgs-dbd-framesp 0 total cursor))))))

(defthm pgs-dbd-core-step-preserves-total
  (equal (pgs-dc-total (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
         (pgs-dc-total pgs-digest-state))
  :hints (("Goal" :in-theory (e/d (pgs-dc-step)
                                   (nth update-nth fn-b3-output fn-b3-output-cv fn-b3-output-root
                                        pgs-octets-be-nat)))))

(defthm pgs-dbd-framesp-zero
  (pgs-dbd-framesp 0 total pgs-digest-state)
  :hints (("Goal" :in-theory (enable pgs-dbd-framesp))))

(defthm pgs-dbd-framesp-of-top-frame-update
  (implies (and (natp index) (equal depth (+ 1 index)))
           (equal (pgs-dbd-framesp depth total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (and (< (fn-b3-nthx 1 frame) total)
                       (pgs-dbd-framesp index total pgs-digest-state))))
  :hints (("Goal"
            :expand ((pgs-dbd-framesp depth total
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                     (:free (cursor) (pgs-dbd-framesp (+ 1 index) total cursor)))
            :in-theory (e/d (pgs-dc-framesi)
                             (nth update-nth pgs-dbd-framesp fn-b3-nthx)))))

(defthm pgs-dbd-core-step-preserves-frames
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (pgs-dbd-framesp (pgs-dc-depth pgs-digest-state)
                                (pgs-dc-total pgs-digest-state) pgs-digest-state))
           (pgs-dbd-framesp (pgs-dc-depth (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                           (pgs-dc-total pgs-digest-state)
                           (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
  :hints (("Goal"
            :use ((:instance pgs-dbd-top-frame-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state)))
                  (:instance pgs-dcd-powerp-bound
                    (power (pgs-dc-power pgs-digest-state))
                    (limit (- (- limit (pgs-dc-depth pgs-digest-state)) 1))))
            :expand ((:free (total cursor)
                       (pgs-dbd-framesp (+ 1 (nth *pgs-dc-depth* pgs-digest-state)) total cursor))
                     (:free (total cursor)
                       (pgs-dbd-framesp (nth *pgs-dc-depth* pgs-digest-state) total cursor)))
            :in-theory (e/d (pgs-dcd-domainp pgs-dc-step pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcd-framesp pgs-dbd-framesp pgs-dcd-powerp
                                  pgs-dbd-top-frame-unfolds pgs-dcd-powerp-bound fn-b3-output
                                  fn-b3-output-cv fn-b3-output-root pgs-octets-be-nat))
            :do-not-induct t)))

; Project only the observed position before opening the domain; digest values
; and other state effects cannot influence this scalar obligation.
(local
 (defthm pgs-dbd-core-step-position-unfolds
  (equal (pgs-dc-pos (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
         (case (pgs-dc-mode pgs-digest-state)
           (:node (if (< 128 (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))
                      (pgs-dc-pos pgs-digest-state) (pgs-dc-start pgs-digest-state)))
           (:chunk (if (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-pos pgs-digest-state)) 8)
                       (pgs-dc-pos pgs-digest-state) (+ 8 (pgs-dc-pos pgs-digest-state))))
           (:return (if (and (not (zp (pgs-dc-depth pgs-digest-state)))
                            (<= (pgs-dc-depth pgs-digest-state) 64)
                            (equal (fn-b3-nthx 0 (pgs-dc-framesi (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)) :left))
                        (nfix (fn-b3-nthx 1 (pgs-dc-framesi (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)))
                      (pgs-dc-pos pgs-digest-state)))
           (otherwise (pgs-dc-pos pgs-digest-state))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pgs-dc-step)
                  (nth update-nth fn-b3-output fn-b3-output-cv fn-b3-output-root
                   pgs-octets-be-nat pgs-dc-pad-block fn-b3-cv8 fn-b3-nthx floor mod expt))))))

(defthm pgs-dbd-core-step-keeps-position-byte-backed
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state))
           (<= (* 8 (pgs-dc-pos (mv-nth 1 (pgs-dc-step block pgs-digest-state)))) byte-total))
  :hints (("Goal"
            :use ((:instance pgs-dbd-core-step-position-unfolds)
                  (:instance pgs-dbd-top-frame-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state)))
                  (:instance pgs-dcd-top-frame-unfolds
                    (depth (pgs-dc-depth pgs-digest-state)) (total (pgs-dc-total pgs-digest-state)))
                  (:instance pgs-dbd-word-before-end-is-byte-backed
                    (word-offset (+ 8 (pgs-dc-pos pgs-digest-state))))
                  (:instance pgs-dbd-word-before-end-is-byte-backed
                    (word-offset (fn-b3-nthx 1 (pgs-dc-framesi
                                      (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)))))
            :in-theory (union-theories (theory 'minimal-theory)
                          '(pgs-dbd-domainp pgs-dcd-domainp natp posp zp nfix
                            member-equal member-eq eql))
            :do-not-induct t)))

(defthm pgs-dbd-tail-update-keeps-page-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :chunk))
           (pgs-dcd-domainp limit
             (update-pgs-dc-mode :return (update-pgs-dc-output out pgs-digest-state))))
  :hints (("Goal" :in-theory (e/d (pgs-dcd-domainp)
                                   (nth update-nth pgs-dcd-framesp pgs-dcd-powerp)))))

(defthm pgs-dbd-tail-raw-update-keeps-page-domain
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (equal (pgs-dc-mode pgs-digest-state) :chunk))
           (pgs-dcd-domainp limit
             (update-nth *pgs-dc-mode* :return
               (update-nth *pgs-dc-output* out pgs-digest-state))))
  :hints (("Goal" :in-theory (e/d (pgs-dcd-domainp)
                                   (nth update-nth pgs-dcd-framesp pgs-dcd-powerp)))))

(defthm pgs-dbd-byte-step-keeps-page-domain
  (implies (pgs-dcd-domainp limit pgs-digest-state)
           (pgs-dcd-domainp limit (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
  :hints (("Goal" :use (pgs-dcd-step-preserves-domain)
                  :in-theory (e/d (pgs-dcb-step)
                                   (nth update-nth pgs-dcd-domainp pgs-dc-step pgs-dcd-step-preserves-domain
                                        fn-b3-output pgs-dc-pad-block fn-b3-cv8)))))

(defthm pgs-dbd-byte-step-preserves-total
  (equal (pgs-dc-total (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
         (pgs-dc-total pgs-digest-state))
  :hints (("Goal" :use pgs-dbd-core-step-preserves-total
                  :in-theory (e/d (pgs-dcb-step)
                                   (nth update-nth pgs-dc-step fn-b3-output pgs-dc-pad-block pgs-dbd-core-step-preserves-total)))))

(defthm pgs-dbd-byte-step-preserves-frames
  (implies (and (pgs-dcd-domainp limit pgs-digest-state)
                (pgs-dbd-framesp (pgs-dc-depth pgs-digest-state)
                                (pgs-dc-total pgs-digest-state) pgs-digest-state))
           (pgs-dbd-framesp (pgs-dc-depth (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                           (pgs-dc-total pgs-digest-state)
                           (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
  :hints (("Goal" :use pgs-dbd-core-step-preserves-frames
                  :in-theory (e/d (pgs-dcb-step)
                                   (nth update-nth pgs-dc-step pgs-dcd-domainp pgs-dbd-framesp
                                        fn-b3-output pgs-dc-pad-block pgs-dbd-core-step-preserves-frames)))))

(defthm pgs-dbd-domain-scalars
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (and (natp byte-total) (natp (pgs-dc-pos pgs-digest-state))
                (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count byte-total))
                (<= (* 8 (pgs-dc-pos pgs-digest-state)) byte-total)
                (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))))
  :hints (("Goal" :in-theory (e/d (pgs-dbd-domainp pgs-dcd-domainp)
                                   (pgs-dbd-framesp pgs-dcd-framesp pgs-dcd-powerp)))))

(defthm pgs-dbd-byte-step-keeps-position-byte-backed
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (<= (* 8 (pgs-dc-pos (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))) byte-total))
  :hints (("Goal" :use (pgs-dbd-core-step-keeps-position-byte-backed pgs-dbd-domain-scalars)
                  :in-theory (e/d (pgs-dcb-step)
                                   (nth update-nth pgs-dc-step pgs-dbd-domainp fn-b3-output
                                        pgs-dc-pad-block pgs-dbd-core-step-keeps-position-byte-backed pgs-dbd-domain-scalars)))))

(defthm pgs-dbd-byte-step-preserves-domain
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (pgs-dbd-domainp limit byte-total
             (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
  :hints (("Goal" :use (pgs-dbd-byte-step-keeps-page-domain
                        pgs-dbd-byte-step-preserves-frames
                        pgs-dbd-byte-step-keeps-position-byte-backed)
                  :in-theory (e/d (pgs-dbd-domainp)
                                   (pgs-dcd-domainp pgs-dbd-framesp pgs-dcb-step
                                        pgs-dbd-byte-step-keeps-page-domain
                                        pgs-dbd-byte-step-preserves-frames
                                        pgs-dbd-byte-step-keeps-position-byte-backed)))))

(defthm pgs-dbd-domain-implies-byte-step-guard
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (and (natp byte-total)
                (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count byte-total))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
                (<= (* 8 (pgs-dc-pos pgs-digest-state)) byte-total)))
  :hints (("Goal" :use pgs-dcd-domain-implies-step-guard
                  :in-theory (e/d (pgs-dbd-domainp)
                                   (pgs-dcd-domainp pgs-dbd-framesp pgs-dcd-domain-implies-step-guard)))))

(defthm pgs-dbd-byte-step-is-never-invalid
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (member-eq (mv-nth 0 (pgs-dcb-step byte-total block pgs-digest-state)) '(:continue :done)))
  :hints (("Goal" :use pgs-dcd-step-is-never-invalid
                  :in-theory (e/d (pgs-dbd-domainp pgs-dcb-step)
                                   (pgs-dcd-domainp pgs-dbd-framesp pgs-dc-step
                                        fn-b3-output pgs-dc-pad-block pgs-dcd-step-is-never-invalid)))))

(in-theory (disable pgs-dbd-domainp pgs-dbd-framesp))
