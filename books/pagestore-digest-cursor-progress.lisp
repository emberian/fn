;; Exact work remaining, proof-only. This never allocates or runs in producer.
(in-package "ACL2")
(include-book "pagestore-digest-cursor-semantics")
(local (include-book "arithmetic-5/top" :dir :system))

(defun-nx pgs-dcs-split-work (power nwords)
  (declare (xargs :measure (nfix (- (nfix nwords) (* 128 (nfix power))))
                  :verify-guards nil))
  (if (and (posp power) (natp nwords) (< (* 256 power) nwords))
      (+ 1 (pgs-dcs-split-work (* 2 power) nwords))
    1))

(defun-nx pgs-dcs-chunk-work (nwords)
  (max 1 (ceiling (nfix nwords) 8)))

(defthm pgs-dcs-node-children-smaller
  (implies (and (natp nwords) (< 128 nwords))
           (let ((left (* 128 (fn-b3-left-chunks 1 (* 8 nwords)))))
             (and (natp left) (< 0 left) (< left nwords)
                  (natp (- nwords left)) (< (- nwords left) nwords))))
  :hints (("Goal" :use ((:instance fn-b3-left-chunks-below (p 1) (n (* 8 nwords))))
                  :in-theory (disable fn-b3-left-chunks)))
  :rule-classes nil)

(defun-nx pgs-dcs-node-work (nwords)
  (declare (xargs :measure (nfix nwords) :verify-guards nil
                  :hints (("Goal" :use pgs-dcs-node-children-smaller
                           :in-theory (union-theories (theory 'minimal-theory)
                                                      '(natp nfix o-p o< o-finp))))))
  (if (and (natp nwords) (< 128 nwords))
      (let* ((left (* 128 (fn-b3-left-chunks 1 (* 8 nwords))))
             (right (- nwords left)))
        (+ 1 (pgs-dcs-split-work 1 nwords)
           (pgs-dcs-node-work left) 1 (pgs-dcs-node-work right) 1))
    (+ 1 (pgs-dcs-chunk-work nwords))))

(defun-nx pgs-dcs-frame-work (depth pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :measure (nfix depth) :verify-guards nil))
  (if (zp depth) 2
    (let* ((index (- depth 1))
           (frame (pgs-dc-framesi index pgs-digest-state)))
      (+ (pgs-dcs-frame-work index pgs-digest-state)
         (if (equal (fn-b3-nthx 0 frame) :left)
             (+ 2 (pgs-dcs-node-work (- (nfix (fn-b3-nthx 2 frame))
                                       (nfix (fn-b3-nthx 1 frame)))))
           1)))))

(defun-nx pgs-dcs-potential (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (let* ((nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))
         (left (* 128 (fn-b3-left-chunks 1 (* 8 nwords)))))
    (case (pgs-dc-mode pgs-digest-state)
      (:done 0)
      (:root 1)
      (otherwise
       (+ (pgs-dcs-frame-work (pgs-dc-depth pgs-digest-state) pgs-digest-state)
          (case (pgs-dc-mode pgs-digest-state)
            (:node (pgs-dcs-node-work nwords))
            (:split (+ (pgs-dcs-split-work (pgs-dc-power pgs-digest-state) nwords)
                       (pgs-dcs-node-work left) 1 (pgs-dcs-node-work (- nwords left)) 1))
            (:chunk (pgs-dcs-chunk-work (- (pgs-dc-end pgs-digest-state)
                                         (pgs-dc-pos pgs-digest-state))))
            (otherwise 0)))))))

(defthm pgs-dcs-frame-work-of-scalar-update
  (implies (and (natp field) (not (equal field *pgs-dc-framesi*)))
           (equal (pgs-dcs-frame-work depth (update-nth field value pgs-digest-state))
                  (pgs-dcs-frame-work depth pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcs-frame-work depth pgs-digest-state)
                  :expand ((pgs-dcs-frame-work depth (update-nth field value pgs-digest-state)))
                  :in-theory (e/d (pgs-dcs-frame-work pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx pgs-dcs-node-work)))))

(defthm pgs-dcs-frame-work-of-frame-update-prefix
  (implies (and (natp index) (<= (nfix depth) index))
           (equal (pgs-dcs-frame-work depth
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state))
                  (pgs-dcs-frame-work depth pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcs-frame-work depth pgs-digest-state)
                  :expand ((pgs-dcs-frame-work depth
                     (update-nth *pgs-dc-framesi*
                       (update-nth index frame (nth *pgs-dc-framesi* pgs-digest-state)) pgs-digest-state)))
                  :in-theory (e/d (pgs-dcs-frame-work pgs-dc-framesi)
                                   (nth update-nth fn-b3-nthx pgs-dcs-node-work)))))

(defthm pgs-dcs-node-work-unfolds
  (equal (pgs-dcs-node-work nwords)
         (if (and (natp nwords) (< 128 nwords))
             (let ((left (* 128 (fn-b3-left-chunks 1 (* 8 nwords)))))
               (+ 1 (pgs-dcs-split-work 1 nwords) (pgs-dcs-node-work left)
                  1 (pgs-dcs-node-work (- nwords left)) 1))
           (+ 1 (pgs-dcs-chunk-work nwords))))
  :hints (("Goal" :expand ((pgs-dcs-node-work nwords))
                  :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm pgs-dcs-node-step-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :node)
                (natp (pgs-dc-start pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-end pgs-digest-state)))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :use ((:instance pgs-dcs-node-work-unfolds
                            (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
                  :in-theory (e/d (pgs-dcs-potential pgs-dc-step)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks))
                  :do-not-induct t)))

(defthm pgs-dcs-split-work-unfolds
  (equal (pgs-dcs-split-work power nwords)
         (if (and (posp power) (natp nwords) (< (* 256 power) nwords))
             (+ 1 (pgs-dcs-split-work (* 2 power) nwords)) 1))
  :hints (("Goal" :expand ((pgs-dcs-split-work power nwords))
                  :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm pgs-dcs-split-search-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :split)
                (posp (pgs-dc-power pgs-digest-state))
                (natp (pgs-dc-start pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (< (* 256 (pgs-dc-power pgs-digest-state))
                   (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :use ((:instance pgs-dcs-split-work-unfolds
                            (power (pgs-dc-power pgs-digest-state))
                            (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
                  :in-theory (e/d (pgs-dcs-potential pgs-dc-step)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks))
                  :do-not-induct t)))

(defthm pgs-dcs-chunk-work-last
  (implies (and (natp nwords) (<= nwords 8))
           (equal (pgs-dcs-chunk-work nwords) 1))
  :hints (("Goal" :in-theory (enable pgs-dcs-chunk-work))))

(defthm pgs-dcs-chunk-work-nonlast
  (implies (and (natp nwords) (< 8 nwords))
           (equal (pgs-dcs-chunk-work (- nwords 8))
                  (- (pgs-dcs-chunk-work nwords) 1)))
  :hints (("Goal" :in-theory (enable pgs-dcs-chunk-work))))

(defthm pgs-dcs-chunk-step-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :chunk)
                (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state)))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-potential pgs-dc-step)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks))
                  :do-not-induct t)))

(defthm pgs-dcs-chunk-last-update-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :chunk)
                (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-pos pgs-digest-state)) 8))
           (equal (pgs-dcs-potential
                    (update-nth *pgs-dc-mode* :return
                      (update-nth *pgs-dc-output* out pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-potential)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks)))))

(defthm pgs-dcs-byte-chunk-step-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :chunk)
                (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state)))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :use pgs-dcs-chunk-step-decreases-potential
                  :in-theory (e/d (pgs-dcb-step)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks
                                        pgs-dc-step pgs-dcs-potential pgs-dcs-chunk-step-decreases-potential))
                  :do-not-induct t)))

(defthm pgs-dcs-split-push-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :split)
                (natp (pgs-dc-start pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))
                (natp (pgs-dc-depth pgs-digest-state)) (< (pgs-dc-depth pgs-digest-state) 64)
                (posp (pgs-dc-power pgs-digest-state))
                (< (* 128 (pgs-dc-power pgs-digest-state))
                   (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))
                (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))
                    (* 256 (pgs-dc-power pgs-digest-state)))
                (equal (fn-b3-left-chunks 1
                         (* 8 (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state))))
                       (pgs-dc-power pgs-digest-state)))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal"
            :use ((:instance pgs-dcs-split-work-unfolds
                    (power (pgs-dc-power pgs-digest-state))
                    (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
            :expand ((:free (cursor)
                      (pgs-dcs-frame-work (+ 1 (nth *pgs-dc-depth* pgs-digest-state)) cursor)))
            :in-theory (e/d (pgs-dcs-potential pgs-dc-step pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                  pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks))
            :do-not-induct t)))

(defthm pgs-dcs-return-empty-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :return)
                (equal (pgs-dc-depth pgs-digest-state) 0))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-potential pgs-dc-step)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-chunk-work fn-b3-left-chunks)))))

(defthm pgs-dcs-root-decreases-potential
  (implies (equal (pgs-dc-mode pgs-digest-state) :root)
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-potential pgs-dc-step)
                                   (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                        pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks)))))

(defthm pgs-dcs-return-left-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :return)
                (posp (pgs-dc-depth pgs-digest-state)) (<= (pgs-dc-depth pgs-digest-state) 64)
                (equal (fn-b3-nthx 0 (pgs-dc-framesi
                                     (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)) :left))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal"
            :expand ((:free (cursor)
                      (pgs-dcs-frame-work (nth *pgs-dc-depth* pgs-digest-state) cursor)))
            :in-theory (e/d (pgs-dcs-potential pgs-dc-step pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                  pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks))
            :do-not-induct t)))

(defthm pgs-dcs-return-right-decreases-potential
  (implies (and (equal (pgs-dc-mode pgs-digest-state) :return)
                (posp (pgs-dc-depth pgs-digest-state)) (<= (pgs-dc-depth pgs-digest-state) 64)
                (not (equal (fn-b3-nthx 0 (pgs-dc-framesi
                                         (- (pgs-dc-depth pgs-digest-state) 1) pgs-digest-state)) :left)))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dc-step block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal"
            :expand ((:free (cursor)
                      (pgs-dcs-frame-work (nth *pgs-dc-depth* pgs-digest-state) cursor)))
            :in-theory (e/d (pgs-dcs-potential pgs-dc-step pgs-dc-framesi update-pgs-dc-framesi)
                             (nth update-nth pgs-dcs-node-work pgs-dcs-split-work
                                  pgs-dcs-frame-work pgs-dcs-chunk-work fn-b3-left-chunks))
            :do-not-induct t)))

(defthm pgs-dcs-split-work-positive
  (and (natp (pgs-dcs-split-work power nwords))
       (< 0 (pgs-dcs-split-work power nwords)))
  :hints (("Goal" :induct (pgs-dcs-split-work power nwords)
                  :in-theory (enable pgs-dcs-split-work)))
  :rule-classes (:rewrite :type-prescription
                 (:linear :corollary (< 0 (pgs-dcs-split-work power nwords)))))

(defthm pgs-dcs-chunk-work-positive
  (and (natp (pgs-dcs-chunk-work nwords)) (< 0 (pgs-dcs-chunk-work nwords)))
  :hints (("Goal" :in-theory (enable pgs-dcs-chunk-work)))
  :rule-classes (:rewrite :type-prescription
                 (:linear :corollary (< 0 (pgs-dcs-chunk-work nwords)))))

(defthm pgs-dcs-node-work-positive
  (and (natp (pgs-dcs-node-work nwords)) (< 0 (pgs-dcs-node-work nwords)))
  :hints (("Goal" :induct (pgs-dcs-node-work nwords)
                  :in-theory (e/d (pgs-dcs-node-work)
                                   (fn-b3-left-chunks pgs-dcs-chunk-work pgs-dcs-split-work))))
  :rule-classes (:rewrite :type-prescription
                 (:linear :corollary (< 0 (pgs-dcs-node-work nwords)))))

(defthm pgs-dcs-frame-work-at-least-two
  (and (natp (pgs-dcs-frame-work depth pgs-digest-state))
       (<= 2 (pgs-dcs-frame-work depth pgs-digest-state)))
  :hints (("Goal" :induct (pgs-dcs-frame-work depth pgs-digest-state)
                  :in-theory (e/d (pgs-dcs-frame-work)
                                   (fn-b3-nthx pgs-dcs-node-work))))
  :rule-classes (:rewrite :type-prescription
                 (:linear :corollary (<= 2 (pgs-dcs-frame-work depth pgs-digest-state)))))

(defthm pgs-dcs-potential-natural
  (natp (pgs-dcs-potential pgs-digest-state))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-potential)
                                   (pgs-dcs-node-work pgs-dcs-split-work pgs-dcs-chunk-work
                                        pgs-dcs-frame-work fn-b3-left-chunks))))
  :rule-classes (:rewrite :type-prescription))

(defthm pgs-dcs-nondone-potential-positive
  (implies (not (equal (pgs-dc-mode pgs-digest-state) :done))
           (< 0 (pgs-dcs-potential pgs-digest-state)))
  :hints (("Goal" :in-theory (e/d (pgs-dcs-potential)
                                   (pgs-dcs-node-work pgs-dcs-split-work pgs-dcs-chunk-work
                                        pgs-dcs-frame-work fn-b3-left-chunks))))
  :rule-classes (:rewrite :linear))

(defthm pgs-dcs-byte-step-decreases-potential
  (implies (and (pgs-dbd-domainp limit byte-total pgs-digest-state)
                (pgs-dcs-phasep pgs-digest-state)
                (not (equal (pgs-dc-mode pgs-digest-state) :done)))
           (equal (pgs-dcs-potential (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                  (- (pgs-dcs-potential pgs-digest-state) 1)))
  :hints (("Goal"
            :use (pgs-dcs-domain-current-unfolds
                  pgs-dcs-node-step-decreases-potential pgs-dcs-split-search-decreases-potential
                  pgs-dcs-split-push-decreases-potential pgs-dcs-byte-chunk-step-decreases-potential
                  pgs-dcs-return-empty-decreases-potential pgs-dcs-return-left-decreases-potential
                  pgs-dcs-return-right-decreases-potential pgs-dcs-root-decreases-potential
                  (:instance pgs-dcr-split-finished-carry-is-power
                    (power (pgs-dc-power pgs-digest-state))
                    (nwords (- (pgs-dc-end pgs-digest-state) (pgs-dc-start pgs-digest-state)))))
            :in-theory (e/d (pgs-dcs-phasep)
                             (nth update-nth fn-b3-nthx pgs-dcs-potential pgs-dbd-domainp
                                  pgs-dcs-node-work pgs-dcs-split-work pgs-dcs-chunk-work
                                  pgs-dcs-frame-work fn-b3-left-chunks pgs-dc-step pgs-dcb-step
                                  pgs-dcb-word-count pgs-dcr-split-finished-carry-is-power
                                  pgs-dcs-node-step-decreases-potential
                                  pgs-dcs-split-search-decreases-potential pgs-dcs-split-push-decreases-potential
                                  pgs-dcs-byte-chunk-step-decreases-potential
                                  pgs-dcs-return-empty-decreases-potential pgs-dcs-return-left-decreases-potential
                                  pgs-dcs-return-right-decreases-potential pgs-dcs-root-decreases-potential))
            :do-not-induct t)))

(defthm pgs-dcs-invariant-step-progress
  (implies (and (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
                (not (equal (pgs-dc-mode pgs-digest-state) :done)))
           (and (natp (pgs-dcs-potential pgs-digest-state))
                (< (pgs-dcs-potential (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state)))
                   (pgs-dcs-potential pgs-digest-state))))
  :hints (("Goal" :use (pgs-dcs-invariant-implies-domain pgs-dcs-invariant-implies-phase
                        pgs-dcs-byte-step-decreases-potential)
                  :in-theory (disable pgs-dcs-invariantp pgs-dcs-phasep pgs-dbd-domainp
                                      pgs-dcs-potential pgs-dcb-step
                                      pgs-dcs-byte-step-decreases-potential)))
  :rule-classes nil)

(defthm pgs-dcs-byte-step-status-matches-mode
  (implies (pgs-dbd-domainp limit byte-total pgs-digest-state)
           (equal (equal (mv-nth 0 (pgs-dcb-step byte-total block pgs-digest-state)) :done)
                  (equal (pgs-dc-mode (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))) :done)))
  :hints (("Goal" :use pgs-dcs-domain-current-unfolds
                  :in-theory (e/d (pgs-dcb-step pgs-dc-step)
                                   (nth update-nth pgs-dbd-domainp fn-b3-output fn-b3-output-cv
                                        fn-b3-output-root pgs-octets-be-nat))
                  :do-not-induct t)))

(defthm pgs-dcs-byte-step-contract
  (implies (and (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
                (pgs-dcs-blockp block msg pgs-digest-state)
                (not (equal (pgs-dc-mode pgs-digest-state) :done)))
           (let* ((step (pgs-dcb-step byte-total block pgs-digest-state))
                  (status (mv-nth 0 step)) (next (mv-nth 1 step)))
             (and (member-eq status '(:continue :done))
                  (equal (equal status :done) (equal (pgs-dc-mode next) :done))
                  (pgs-dcs-invariantp limit byte-total msg next)
                  (equal (pgs-dcr-denote msg next) (pgs-dcr-denote msg pgs-digest-state))
                  (equal (pgs-dc-capture next) (pgs-dc-capture pgs-digest-state))
                  (equal (pgs-dc-lease next) (pgs-dc-lease pgs-digest-state))
                  (equal (pgs-dcs-potential next) (- (pgs-dcs-potential pgs-digest-state) 1))
                  (< (pgs-dcs-potential next) (pgs-dcs-potential pgs-digest-state)))))
  :hints (("Goal" :use (pgs-dcs-invariant-implies-domain pgs-dcs-invariant-implies-phase
                        pgs-dbd-byte-step-is-never-invalid pgs-dcs-byte-step-status-matches-mode
                        pgs-dcs-byte-step-preserves-invariant pgs-dcs-byte-step-preserves-denotation
                        pgs-dcb-step-preserves-capture-and-lease pgs-dcs-byte-step-decreases-potential
                        pgs-dcs-invariant-step-progress)
                  :in-theory (e/d (pgs-dcs-invariantp)
                                   (nth update-nth pgs-dc-mode pgs-dcs-byte-step-outside-tail-is-page-step
                                        pgs-dbd-domainp pgs-dcs-phasep pgs-dcs-blockp pgs-dcr-denote
                                        pgs-dcs-potential pgs-dcb-step fn-b3-node
                                        pgs-dbd-byte-step-is-never-invalid
                                        pgs-dcs-byte-step-status-matches-mode
                                        pgs-dcs-byte-step-preserves-invariant
                                        pgs-dcs-byte-step-preserves-denotation
                                        pgs-dcb-step-preserves-capture-and-lease
                                        pgs-dcs-byte-step-decreases-potential))))
  :rule-classes nil)

(defun-nx pgs-dcs-next-block (msg pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (if (pgs-dc-needs-block pgs-digest-state)
      (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos pgs-digest-state)
                                     (pgs-dc-end pgs-digest-state) msg))
    nil))

(defthm pgs-dcs-next-block-satisfies-contract
  (pgs-dcs-blockp (pgs-dcs-next-block msg pgs-digest-state) msg pgs-digest-state)
  :hints (("Goal" :in-theory (e/d (pgs-dcs-blockp pgs-dcs-next-block)
                                   (pgs-dcr-span pgs-dc-needs-block fn-b3-words)))))

;; This logical driver is the induction principle over the ACTUAL byte step.
;; It neither executes in the producer nor accepts an arbitrary fuel ceiling.
(defun-nx pgs-dcs-finish (limit byte-total msg pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil
                  :measure (pgs-dcs-potential pgs-digest-state)
                  :hints (("Goal" :use ((:instance pgs-dcs-invariant-step-progress
                                          (block (pgs-dcs-next-block msg pgs-digest-state))))
                           :in-theory (disable pgs-dcs-invariantp pgs-dcs-potential
                                               pgs-dcs-next-block pgs-dcb-step)))))
  (if (or (not (pgs-dcs-invariantp limit byte-total msg pgs-digest-state))
          (equal (pgs-dc-mode pgs-digest-state) :done))
      pgs-digest-state
    (pgs-dcs-finish limit byte-total msg
      (mv-nth 1 (pgs-dcb-step byte-total (pgs-dcs-next-block msg pgs-digest-state) pgs-digest-state)))))

(defthm pgs-dcs-finish-preserves-invariant-and-reaches-done
  (implies (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
           (let ((final (pgs-dcs-finish limit byte-total msg pgs-digest-state)))
             (and (pgs-dcs-invariantp limit byte-total msg final)
                  (equal (pgs-dc-mode final) :done))))
  :hints (("Goal" :induct (pgs-dcs-finish limit byte-total msg pgs-digest-state)
                  :in-theory (e/d (pgs-dcs-finish)
                                   (nth pgs-dc-mode pgs-dcs-invariantp pgs-dcs-next-block pgs-dcb-step
                                        pgs-dcs-byte-step-outside-tail-is-page-step)))))

(defthm pgs-dcs-complete-byte-run-is-blake3
  (implies (and (natp limit) (<= limit 63)
                (fn-b3-octet-listp msg) (equal (len msg) byte-total)
                (<= (pgs-dcb-word-count byte-total) (* 128 (expt 2 limit))))
           (equal (pgs-dcb-result-octets
                    (pgs-dcs-finish limit byte-total msg
                      (pgs-dcb-begin sel base byte-total capture lease pgs-digest-state)))
                  (fn-blake3 msg)))
  :hints (("Goal" :use ((:instance pgs-dcs-finish-preserves-invariant-and-reaches-done
                          (pgs-digest-state (pgs-dcb-begin sel base byte-total capture lease pgs-digest-state)))
                        (:instance pgs-dcs-done-result-is-blake3
                          (pgs-digest-state
                            (pgs-dcs-finish limit byte-total msg
                              (pgs-dcb-begin sel base byte-total capture lease pgs-digest-state)))))
                  :in-theory (disable pgs-dcs-invariantp pgs-dcs-finish pgs-dcb-begin
                                      pgs-dcb-result-octets fn-blake3 pgs-dcb-word-count
                                      pgs-dcs-finish-preserves-invariant-and-reaches-done
                                      pgs-dcs-done-result-is-blake3)))
  :rule-classes nil)

(in-theory (disable pgs-dcs-split-work pgs-dcs-chunk-work pgs-dcs-node-work
                    pgs-dcs-frame-work pgs-dcs-potential pgs-dcs-next-block pgs-dcs-finish))
