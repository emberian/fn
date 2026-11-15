; Actual retained-event root source construction. Semantic coverage is the
; authenticated reader terminal; physical page completion belongs to the shared
; owned-buffer worker. No caller-selected root/count/readiness is accepted.
(in-package "ACL2")
(include-book "event-build-state")
(include-book "event-frontier-source")
(include-book "event-frontier-ref-fields")
(include-book "release-inventory-source")
(include-book "checkpoint-page-header")
(include-book "checkpoint-map-build")
(include-book "checkpoint-source-retention")
(fn2-book-layer :c)

(defun fn2-event-build-ownerp (fn2-event-build fn2-csnapshot fn2-checkpoints)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints)
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints))))
 (and (< 0 (fn2-event-build-rows fn2-event-build))
      (fn2-csnapshot-ownerp (fn2-event-build-token 0 fn2-event-build)
       (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
       (fn2-event-build-owner-gen 0 fn2-event-build) fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
      (equal (fn2-event-build-cut-commit 0 fn2-event-build) (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
      (equal (fn2-event-build-cut-event 0 fn2-event-build) (fn2-csnapshot-cut-event 0 fn2-csnapshot))
      (fn2-checkpoint-builder-ownerp (fn2-event-build-candidate 0 fn2-event-build) (fn2-event-build-token 0 fn2-event-build)
       (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
       (fn2-event-build-owner-gen 0 fn2-event-build) fn2-checkpoints)
      (equal (fn2-event-build-history 0 fn2-event-build) (fn2-checkpoints-history (fn2-event-build-candidate 0 fn2-event-build) fn2-checkpoints))
      (equal (fn2-event-build-history-incarnation 0 fn2-event-build) (fn2-checkpoints-incarnation (fn2-event-build-candidate 0 fn2-event-build) fn2-checkpoints))))

(defun fn2-event-build-begin (c token slot gen scratch sgen okind oslot ogen
                             fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                             fn2-mk fn2-fc fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-mk fn2-fc fn2-digests fn2-pool) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-mk-wfp fn2-mk) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (< 0 (fn2-event-build-rows fn2-event-build))
                     (member-equal (fn2-event-build-phase 0 fn2-event-build)
                      (list *fn2-event-build-phase-idle* *fn2-event-build-phase-auth-ready*))
                     (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (fn2-checkpoint-builder-ownerp c token okind oslot ogen fn2-checkpoints)
                     (fn2-origin-physicalp (fn2-checkpoints-history c fn2-checkpoints) (fn2-checkpoints-incarnation c fn2-checkpoints))
                     (fn2-event-frontier-source-p token okind oslot ogen fn2-event-read fn2-csnapshot fn2-mk fn2-fc fn2-digests)))
       (mv :source fn2-event-build))
      (cut (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
      (pages (fn2-checkpoint-map-page-count cut *fn2-event-proof-slots*))
      ((unless (and (unsigned-byte-p 60 pages) (unsigned-byte-p 60 (* pages *fn2-format-page-size*))
                     (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (unsigned-byte-p 32 scratch) (unsigned-byte-p 60 sgen)
                     (not (equal slot scratch)) (eq (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
                     (eq (fn2-pool-workspace-code scratch sgen okind oslot ogen fn2-pool) :ok)
                     (<= *fn2-format-page-size* (fn2-pool-cap slot fn2-pool)) (<= 32 (fn2-pool-cap scratch fn2-pool))))
       (mv :bounds fn2-event-build))
      (fn2-event-build (fn2-event-build-put 0
       (phase (if (equal cut 0) *fn2-event-build-phase-reserve* *fn2-event-build-phase-claim-zero*))
       (token token) (owner-kind okind) (owner-slot oslot) (owner-gen ogen) (candidate c)
       (cut-commit cut) (cut-event (fn2-csnapshot-cut-event 0 fn2-csnapshot))
       (slot slot) (gen gen) (scratch scratch) (scratch-gen sgen)
       (role 3) (ordinal (- pages 1)) (pages pages) (first 0) (end 0) (entry 0)
       (claimed 0) (zero 0) (peak 0) (payload 0) (has-child 0)
       (directory-completed 0) (frontier-completed 0) (history (fn2-checkpoints-history c fn2-checkpoints)) (history-incarnation (fn2-checkpoints-incarnation c fn2-checkpoints)))))
  (mv :ok fn2-event-build)))

(defun fn2-event-build-reserve (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-control)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-control) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-control-wfp fn2-control))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-reserve*)
                     (equal (fn2-event-build-claimed 0 fn2-event-build) (fn2-event-build-cut-commit 0 fn2-event-build))))
       (mv :state fn2-event-build fn2-checkpoint-construction fn2-extents fn2-control))
      (role (fn2-event-build-role 0 fn2-event-build)) (ordinal (fn2-event-build-ordinal 0 fn2-event-build))
      (pages (fn2-event-build-pages 0 fn2-event-build))
      (first (* (fn2-event-build-ordinal 0 fn2-event-build) *fn2-event-proof-slots*))
      (end (min (+ first *fn2-event-proof-slots*) (fn2-event-build-cut-commit 0 fn2-event-build)))
      ((unless (and (member-equal role '(3 4))
                     (equal pages (fn2-checkpoint-map-page-count (fn2-event-build-cut-commit 0 fn2-event-build) *fn2-event-proof-slots*))
                     (unsigned-byte-p 60 (* pages *fn2-format-page-size*))
                     (unsigned-byte-p 60 first) (unsigned-byte-p 60 end) (<= first end)
                     (if (equal role 3)
                         (and (< ordinal pages)
                              (equal (fn2-event-build-directory-completed 0 fn2-event-build) (* (- pages (+ ordinal 1)) *fn2-format-page-size*)))
                       (and (equal ordinal 0) (equal (fn2-event-build-directory-completed 0 fn2-event-build) (* pages *fn2-format-page-size*))
                            (equal (fn2-event-build-frontier-completed 0 fn2-event-build) 0)))))
       (mv :bounds fn2-event-build fn2-checkpoint-construction fn2-extents fn2-control))
      ((mv code e ep al fn2-checkpoint-construction fn2-extents fn2-control)
       (fn2-checkpoint-construction-reserve (fn2-event-build-token 0 fn2-event-build)
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build) (fn2-event-build-role 0 fn2-event-build)
        (fn2-event-build-ordinal 0 fn2-event-build) *fn2-format-page-size*
        fn2-csnapshot fn2-checkpoint-construction fn2-extents fn2-control))
      ((when (member-eq code '(:no-space :exhausted)))
       ; An actionable refusal, not progress or an implicit retry while held.
       (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-control))
      (fn2-event-build (fn2-event-build-put 0
       (extent e) (epoch ep) (allocation al) (zero 0) (peak 0) (first first) (end end) (entry first)
       (phase (if (eq code :ok) *fn2-event-build-phase-zero* *fn2-event-build-phase-uncertain*)))))
  (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-control)))

(defun fn2-event-build-zero-step (budget fn2-event-build fn2-csnapshot fn2-checkpoints fn2-pool)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-pool) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (member-equal (fn2-event-build-phase 0 fn2-event-build)
                      (list *fn2-event-build-phase-claim-zero* *fn2-event-build-phase-zero*))))
       (mv :state fn2-event-build fn2-pool))
      ((unless (posp budget)) (mv :yield fn2-event-build fn2-pool))
      (at (fn2-event-build-zero 0 fn2-event-build))
      ((unless (< at *fn2-format-page-size*)) (mv :bounds fn2-event-build fn2-pool))
      (n (min 4096 (min budget (- *fn2-format-page-size* at))))
      ((mv code fn2-pool) (fn2-run-zero n (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build) at
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build) fn2-pool))
      (done (equal (+ at n) *fn2-format-page-size*))
      (claiming (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-claim-zero*))
      (fn2-event-build (fn2-event-build-put 0 (zero (if (eq code :ok) (+ at n) at))
       (phase (if (not (eq code :ok)) *fn2-event-build-phase-uncertain*
                (if (not done) (fn2-event-build-phase 0 fn2-event-build)
                 (if claiming *fn2-event-build-phase-claims*
                  (if (equal (fn2-event-build-role 0 fn2-event-build) 3) *fn2-event-build-phase-entries* *fn2-event-build-phase-frontier-header*))))))))
  (mv (if (eq code :ok) :more code) fn2-event-build fn2-pool)))

(defun fn2-event-build-entry-step (budget base fn2-event-build fn2-csnapshot fn2-checkpoints fn2-commit-root
                                  fn2-extents fn2-alloc-edges fn2-ops fn2-fc fn2-digests fn2-fields fn2-pool fn2-checkpoint-summary-authority fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-commit-root fn2-extents fn2-alloc-edges
                          fn2-ops fn2-fc fn2-digests fn2-fields fn2-pool fn2-checkpoint-summary-authority fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-commit-root-wfp fn2-commit-root) (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-ops-wfp fn2-ops) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-restore-events-wfp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (member-equal (fn2-event-build-phase 0 fn2-event-build)
                      (list *fn2-event-build-phase-claims* *fn2-event-build-phase-entries*))))
       (mv :state fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool))
      ((unless (posp budget)) (mv :yield fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool))
      (claiming (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-claims*))
      (entry (if claiming (fn2-event-build-claimed 0 fn2-event-build) (fn2-event-build-entry 0 fn2-event-build)))
      (end (if claiming (fn2-event-build-cut-commit 0 fn2-event-build) (fn2-event-build-end 0 fn2-event-build)))
      ((when (equal entry end))
       (let ((fn2-event-build (fn2-event-build-set-phase 0
               (if claiming *fn2-event-build-phase-reserve* *fn2-event-build-phase-directory-header*) fn2-event-build)))
        (mv :more fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool)))
      ((unless (< entry end)) (mv :coverage fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool))
      ((mv packed & fn2-fields fn2-pool)
       (fn2-event-proof-pack-entry (fn2-event-build-token 0 fn2-event-build) entry base
        (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build)
        (+ *fn2-checkpoint-map-entries-start* (* (mod entry *fn2-event-proof-slots*) *fn2-event-proof-entry-width*))
        (fn2-event-build-scratch 0 fn2-event-build) (fn2-event-build-scratch-gen 0 fn2-event-build)
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build)
        fn2-csnapshot fn2-commit-root fn2-extents fn2-alloc-edges fn2-fc fn2-digests fn2-fields fn2-pool fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-ops))
      ((unless (eq packed :ok))
       (let ((fn2-event-build (fn2-event-build-set-phase 0 *fn2-event-build-phase-uncertain* fn2-event-build)))
        (mv packed fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool)))
      ((mv code fn2-extents fn2-alloc-edges)
       (if claiming
           (fn2-checkpoint-source-claim (fn2-event-build-candidate 0 fn2-event-build)
            (fn2-checkpoints-checkpoint (fn2-event-build-candidate 0 fn2-event-build) fn2-checkpoints)
            (fn2-fields-value (+ base *fn2-event-proof-entry-field-extent*) fn2-fields)
            (fn2-fields-value (+ base *fn2-event-proof-entry-field-writer-epoch*) fn2-fields)
            (fn2-fields-value (+ base *fn2-event-proof-entry-field-allocation*) fn2-fields)
            fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoints)
         (mv :ok fn2-extents fn2-alloc-edges)))
      (fn2-event-build (cond ((not (eq code :ok)) (fn2-event-build-set-phase 0 *fn2-event-build-phase-uncertain* fn2-event-build))
                            (claiming (fn2-event-build-set-claimed 0 (+ 1 entry) fn2-event-build))
                            (t (fn2-event-build-set-entry 0 (+ 1 entry) fn2-event-build)))))
  (mv (if (eq code :ok) :more code) fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool)))

(defun fn2-event-build-directory-header (budget base fn2-event-build fn2-csnapshot fn2-checkpoints
                                        fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents
                          fn2-checkpoint-page-verified fn2-fields fn2-pool) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-directory-header*)
                     (equal (fn2-event-build-role 0 fn2-event-build) 3)
                     (equal (fn2-event-build-zero 0 fn2-event-build) *fn2-format-page-size*)
                     (equal (fn2-event-build-entry 0 fn2-event-build) (fn2-event-build-end 0 fn2-event-build))
                     (equal (fn2-event-build-claimed 0 fn2-event-build) (fn2-event-build-cut-commit 0 fn2-event-build))
                     (equal (fn2-event-build-has-child 0 fn2-event-build)
                            (if (< (+ 1 (fn2-event-build-ordinal 0 fn2-event-build)) (fn2-event-build-pages 0 fn2-event-build)) 1 0))))
       (mv :coverage fn2-event-build fn2-fields fn2-pool))
      ((unless (and (natp budget) (<= *fn2-checkpoint-map-header-max-size* budget)))
       (mv :yield fn2-event-build fn2-fields fn2-pool))
      (count (- (fn2-event-build-end 0 fn2-event-build) (fn2-event-build-first 0 fn2-event-build)))
      ((mv code fn2-fields fn2-pool)
       (fn2-checkpoint-linked-header-pack (fn2-event-build-token 0 fn2-event-build)
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build) 3 (fn2-event-build-ordinal 0 fn2-event-build)
        (fn2-event-build-extent 0 fn2-event-build) (fn2-event-build-epoch 0 fn2-event-build)
        (fn2-event-build-allocation 0 fn2-event-build) (fn2-event-build-history 0 fn2-event-build) (fn2-event-build-history-incarnation 0 fn2-event-build)
        (fn2-event-build-cut-commit 0 fn2-event-build) (fn2-event-build-cut-event 0 fn2-event-build)
        (fn2-event-build-cut-commit 0 fn2-event-build) (fn2-event-build-first 0 fn2-event-build) count *fn2-event-proof-slots* base
        (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build)
        (fn2-event-build-scratch 0 fn2-event-build) (fn2-event-build-scratch-gen 0 fn2-event-build)
        (fn2-event-build-child 0 fn2-event-build)
        fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-fields fn2-pool))
      (fn2-event-build (if (eq code :ok)
       (fn2-event-build-put 0
        (payload (+ (- *fn2-checkpoint-map-entries-start* *fn2-checkpoint-map-body-start*) (* count *fn2-event-proof-entry-width*)))
        (phase *fn2-event-build-phase-physical-header*))
       (fn2-event-build-set-phase 0 *fn2-event-build-phase-uncertain* fn2-event-build))))
  (mv (if (eq code :ok) :more code) fn2-event-build fn2-fields fn2-pool)))

(defun fn2-event-build-frontier-header (budget base fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints
                                       fn2-checkpoint-refs fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified
                                       fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-release-inventory-build)
 (declare (xargs :stobjs (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs
                          fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-release-inventory-build)
  :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-mk-wfp fn2-mk) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-event-buildp fn2-event-build) (fn2-event-readp fn2-event-read) (fn2-csnapshotp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-mkp fn2-mk) (fn2-fcp fn2-fc) (fn2-digestsp fn2-digests) (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-frontier-header*)
                     (equal (fn2-event-build-role 0 fn2-event-build) 4)
                     (equal (fn2-event-build-zero 0 fn2-event-build) *fn2-format-page-size*)
                     (fn2-event-frontier-source-p (fn2-event-build-token 0 fn2-event-build)
                      (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
                      (fn2-event-build-owner-gen 0 fn2-event-build) fn2-event-read fn2-csnapshot fn2-mk fn2-fc fn2-digests)))
       (mv :source fn2-event-build fn2-fields fn2-pool))
      ((unless (and (natp budget) (<= *fn2-event-frontier-header-max-size* budget)))
       (mv :yield fn2-event-build fn2-fields fn2-pool))
      ((unless (and (natp base) (<= (+ base *fn2-event-frontier-header-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-event-build fn2-fields fn2-pool))
      (token (fn2-event-build-token 0 fn2-event-build)) (kind (fn2-event-build-owner-kind 0 fn2-event-build))
      (owner (fn2-event-build-owner-slot 0 fn2-event-build)) (generation (fn2-event-build-owner-gen 0 fn2-event-build))
      (r (+ (* 6 (fn2-event-build-candidate 0 fn2-event-build)) 3))
      ((unless (< r (fn2-checkpoint-refs-rows fn2-checkpoint-refs))) (mv :bounds fn2-event-build fn2-fields fn2-pool))
      (unit (fn2-checkpoint-refs-physical-unit r fn2-checkpoint-refs)) (child (floor unit *fn2-storage-extent-units*))
      ((unless (and (equal (mod unit *fn2-storage-extent-units*) 0)
                     (equal (fn2-checkpoint-refs-root-build-token r fn2-checkpoint-refs) token)
                     (equal (fn2-checkpoint-refs-root-source-complete r fn2-checkpoint-refs) 1)
                     (equal (fn2-checkpoint-refs-root-intended-bytes r fn2-checkpoint-refs) (* (fn2-event-build-pages 0 fn2-event-build) *fn2-format-page-size*))
                     (equal (fn2-checkpoint-refs-root-completed-bytes r fn2-checkpoint-refs) (fn2-checkpoint-refs-root-intended-bytes r fn2-checkpoint-refs))
                     (equal (fn2-event-build-directory-completed 0 fn2-event-build) (fn2-checkpoint-refs-root-completed-bytes r fn2-checkpoint-refs))
                     (equal (fn2-checkpoint-refs-storage-domain r fn2-checkpoint-refs) *fn2-checkpoint-served-storage-domain*)
                     (equal (fn2-checkpoint-refs-page-kind r fn2-checkpoint-refs) *page-kind-manifest*)
                     (equal (fn2-checkpoint-refs-encoded-length r fn2-checkpoint-refs) *fn2-format-page-size*)
                     (fn2-checkpoint-page-completed-extent-p token kind owner generation 3 0 child fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents)
                     (equal (fn2-checkpoint-page-verified-page-kind child fn2-checkpoint-page-verified) *page-kind-manifest*)
                     (equal (fn2-checkpoint-page-verified-history child fn2-checkpoint-page-verified) (fn2-event-build-history 0 fn2-event-build))
                     (equal (fn2-checkpoint-page-verified-incarnation child fn2-checkpoint-page-verified) (fn2-event-build-history-incarnation 0 fn2-event-build))
                     (equal (fn2-checkpoint-page-verified-encoded-length child fn2-checkpoint-page-verified) *fn2-format-page-size*)
                     (equal (fn2-checkpoint-refs-writer-epoch r fn2-checkpoint-refs) (fn2-checkpoint-page-verified-epoch child fn2-checkpoint-page-verified))
                     (equal (fn2-checkpoint-refs-allocation r fn2-checkpoint-refs) (fn2-checkpoint-page-verified-allocation child fn2-checkpoint-page-verified))))
       (mv :directory fn2-event-build fn2-fields fn2-pool))
      ((unless (and (fn2-release-inventory-complete-p fn2-release-inventory-build fn2-csnapshot fn2-checkpoints
                       fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified)
                     (equal (fn2-release-inventory-build-token 0 fn2-release-inventory-build) token)
                     (equal (fn2-release-inventory-build-candidate 0 fn2-release-inventory-build) (fn2-event-build-candidate 0 fn2-event-build))))
       (mv :inventory fn2-event-build fn2-fields fn2-pool))
      (inventory-head (fn2-release-inventory-build-head 0 fn2-release-inventory-build))
      (slot (fn2-event-build-slot 0 fn2-event-build)) (gen (fn2-event-build-gen 0 fn2-event-build))
      (scratch (fn2-event-build-scratch 0 fn2-event-build)) (sgen (fn2-event-build-scratch-gen 0 fn2-event-build))
      ((mv reset fn2-pool) (fn2-pool-reset scratch sgen kind owner generation fn2-pool))
      ((unless (eq reset :ok)) (mv reset fn2-event-build fn2-fields fn2-pool))
      ((mv copied fn2-pool) (fn2-checkpoint-linked-hash-buffer 32 0 0 child scratch sgen kind owner generation nil fn2-checkpoint-page-verified fn2-pool))
      ((unless (eq copied :ok)) (mv copied fn2-event-build fn2-fields fn2-pool))
      ((mv copied fn2-pool) (fn2-checkpoint-linked-hash-buffer 32 0 32 inventory-head scratch sgen kind owner generation nil fn2-checkpoint-page-verified fn2-pool))
      ((unless (eq copied :ok)) (mv copied fn2-event-build fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-event-frontier-header-field-kind*) *checkpoint-event-frontier-kind-semantic-member-frontier* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-event-frontier-header-field-version*) *fn2-format-version* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-event-frontier-header-field-cut-commit*) (fn2-event-build-cut-commit 0 fn2-event-build) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-event-frontier-header-field-cut-event*) (fn2-event-build-cut-event 0 fn2-event-build) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-event-frontier-header-field-leaf-count*) (fn2-mk-size (fn2-b-event-row (fn2-fc-rows fn2-fc)) fn2-mk) fn2-fields))
      (fn2-fields (fn2-event-frontier-put-ref "DIRECTORY-" base child 0 scratch sgen))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-event-frontier-header-field-inventory-count*)
                    (fn2-release-inventory-build-count 0 fn2-release-inventory-build) fn2-fields))
      (fn2-fields (fn2-event-frontier-put-ref "INVENTORY-" base inventory-head 32 scratch sgen))
      ((mv code next fn2-pool) (fn2-event-frontier-header-encode base slot gen *fn2-checkpoint-map-body-start* kind owner generation fn2-fields fn2-pool))
      (good (and (eq code :ok) (<= next *fn2-event-frontier-peaks-start*)))
      (fn2-event-build (if good (fn2-event-build-put 0 (peak 0)
        (payload (- (+ *fn2-event-frontier-peaks-start* (* 60 32)) *fn2-checkpoint-page-header-area*))
        (phase *fn2-event-build-phase-peaks*))
        (fn2-event-build-set-phase 0 *fn2-event-build-phase-uncertain* fn2-event-build))))
  (mv (if good :more :format) fn2-event-build fn2-fields fn2-pool)))

(defun fn2-event-build-peak-step (budget fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-mk fn2-fc fn2-digests fn2-pool)
 (declare (xargs :stobjs (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-mk fn2-fc fn2-digests fn2-pool) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-mk-wfp fn2-mk) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-peaks*)))
       (mv :state fn2-event-build fn2-pool))
      (peak (fn2-event-build-peak 0 fn2-event-build))
      ((when (equal peak 60))
       (let ((fn2-event-build (fn2-event-build-set-phase 0 *fn2-event-build-phase-physical-header* fn2-event-build)))
        (mv :more fn2-event-build fn2-pool)))
      ((unless (< peak 60)) (mv :bounds fn2-event-build fn2-pool))
      ((unless (and (natp budget) (<= 32 budget))) (mv :yield fn2-event-build fn2-pool))
      ((mv code fn2-pool)
       (fn2-event-frontier-pack-peak (fn2-event-build-token 0 fn2-event-build) peak
        (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build)
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build) fn2-event-read fn2-csnapshot fn2-mk fn2-fc fn2-digests fn2-pool))
      (fn2-event-build (if (eq code :ok) (fn2-event-build-set-peak 0 (+ 1 peak) fn2-event-build)
                        (fn2-event-build-set-phase 0 *fn2-event-build-phase-uncertain* fn2-event-build))))
  (mv (if (eq code :ok) :more code) fn2-event-build fn2-pool)))

(defun fn2-event-build-physical-header (budget base fn2-event-build fn2-csnapshot fn2-checkpoints
                                       fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-physical-header*)
                     (member-equal (fn2-event-build-role 0 fn2-event-build) '(3 4))))
       (mv :state fn2-event-build fn2-fields fn2-pool))
      ((unless (and (natp budget) (<= *fn2-format-page-header-max-size* budget)))
       (mv :yield fn2-event-build fn2-fields fn2-pool))
      ((mv code fn2-fields fn2-pool)
       (fn2-checkpoint-page-pack-header (fn2-event-build-token 0 fn2-event-build)
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build) (fn2-event-build-role 0 fn2-event-build)
        (fn2-event-build-ordinal 0 fn2-event-build) (fn2-event-build-extent 0 fn2-event-build)
        (fn2-event-build-epoch 0 fn2-event-build) (fn2-event-build-allocation 0 fn2-event-build)
        (if (equal (fn2-event-build-role 0 fn2-event-build) 3) *page-kind-manifest* *page-kind-merkle-node*)
        (fn2-event-build-history 0 fn2-event-build) (fn2-event-build-history-incarnation 0 fn2-event-build) *fn2-format-page-size* (fn2-event-build-payload 0 fn2-event-build) base
        (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build)
        fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool))
      (fn2-event-build (fn2-event-build-set-phase 0
        (if (eq code :ok) *fn2-event-build-phase-page* *fn2-event-build-phase-uncertain*) fn2-event-build)))
  (mv (if (eq code :ok) :page code) fn2-event-build fn2-fields fn2-pool)))

; Bind once. No source packing transition exists in :bound while the shared
; worker owns the real HAND/ACCEPT lease or while its write result is pending.
(defun fn2-event-build-bind-page (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents
                                 fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields)
 (declare (xargs :stobjs (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents
                          fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc) (fn2-fields-wfp fn2-fields))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-page*)
                     (member-equal (fn2-event-build-role 0 fn2-event-build) '(3 4))))
       (mv :state fn2-event-build fn2-checkpoint-page))
      ((mv code fn2-checkpoint-page)
       (fn2-checkpoint-page-begin (fn2-event-build-token 0 fn2-event-build)
        (fn2-event-build-owner-kind 0 fn2-event-build) (fn2-event-build-owner-slot 0 fn2-event-build)
        (fn2-event-build-owner-gen 0 fn2-event-build) (fn2-event-build-role 0 fn2-event-build)
        (fn2-event-build-ordinal 0 fn2-event-build) (fn2-event-build-extent 0 fn2-event-build)
        (fn2-event-build-epoch 0 fn2-event-build) (fn2-event-build-allocation 0 fn2-event-build)
        (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build)
        (if (equal (fn2-event-build-role 0 fn2-event-build) 3) *page-kind-manifest* *page-kind-merkle-node*)
        (fn2-event-build-history 0 fn2-event-build) (fn2-event-build-history-incarnation 0 fn2-event-build) *fn2-format-page-size* fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction
        fn2-csnapshot fn2-extents fn2-pool fn2-fc fn2-fields))
      (fn2-event-build (if (eq code :ok) (fn2-event-build-set-phase 0 *fn2-event-build-phase-bound* fn2-event-build) fn2-event-build)))
  (mv code fn2-event-build fn2-checkpoint-page)))

(defun fn2-event-build-consume-page (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                    fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-mk fn2-fc fn2-digests fn2-pool fn2-release-inventory-build)
 (declare (xargs :stobjs (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                          fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-mk fn2-fc fn2-digests fn2-pool fn2-release-inventory-build)
  :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-mk-wfp fn2-mk) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-pool-wfp fn2-pool) (fn2-event-buildp fn2-event-build) (fn2-event-readp fn2-event-read) (fn2-csnapshotp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-pagep fn2-checkpoint-page) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-mkp fn2-mk) (fn2-fcp fn2-fc) (fn2-digestsp fn2-digests) (fn2-poolp fn2-pool) (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build))))
 (b* (((unless (and (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints)
                     (equal (fn2-event-build-phase 0 fn2-event-build) *fn2-event-build-phase-bound*)))
       (mv :state fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes))
      (token (fn2-event-build-token 0 fn2-event-build)) (kind (fn2-event-build-owner-kind 0 fn2-event-build))
      (owner (fn2-event-build-owner-slot 0 fn2-event-build)) (generation (fn2-event-build-owner-gen 0 fn2-event-build))
      (c (fn2-event-build-candidate 0 fn2-event-build)) (role (fn2-event-build-role 0 fn2-event-build))
      (ordinal (fn2-event-build-ordinal 0 fn2-event-build)) (e (fn2-event-build-extent 0 fn2-event-build))
      (r (+ (* 6 c) role)) (pages (fn2-event-build-pages 0 fn2-event-build))
      ((unless (and (member-equal role '(3 4))
                     (fn2-checkpoint-slotp c fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
                     (fn2-event-frontier-source-p token kind owner generation fn2-event-read fn2-csnapshot fn2-mk fn2-fc fn2-digests)
                     (equal (fn2-event-build-claimed 0 fn2-event-build) (fn2-event-build-cut-commit 0 fn2-event-build))
                     (equal pages (fn2-checkpoint-map-page-count (fn2-event-build-cut-commit 0 fn2-event-build) *fn2-event-proof-slots*))
                     (unsigned-byte-p 60 (* pages *fn2-format-page-size*))
                     (fn2-checkpoint-page-completed-extent-p token kind owner generation role ordinal e fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents)
                     (equal (fn2-checkpoint-page-verified-epoch e fn2-checkpoint-page-verified) (fn2-event-build-epoch 0 fn2-event-build))
                     (equal (fn2-checkpoint-page-verified-allocation e fn2-checkpoint-page-verified) (fn2-event-build-allocation 0 fn2-event-build))
                     (equal (fn2-checkpoint-page-verified-page-kind e fn2-checkpoint-page-verified) (if (equal role 3) *page-kind-manifest* *page-kind-merkle-node*))
                     (equal (fn2-checkpoint-page-verified-history e fn2-checkpoint-page-verified) (fn2-event-build-history 0 fn2-event-build))
                     (equal (fn2-checkpoint-page-verified-incarnation e fn2-checkpoint-page-verified) (fn2-event-build-history-incarnation 0 fn2-event-build))
                     (equal (fn2-checkpoint-page-verified-encoded-length e fn2-checkpoint-page-verified) *fn2-format-page-size*)
                     (eq (fn2-pool-workspace-code (fn2-event-build-slot 0 fn2-event-build) (fn2-event-build-gen 0 fn2-event-build)
                           kind owner generation fn2-pool) :ok)
                     (< 0 (fn2-checkpoint-page-rows fn2-checkpoint-page))
                     (or (not (equal (fn2-checkpoint-page-extent 0 fn2-checkpoint-page) e))
                         (equal (fn2-checkpoint-page-transferred 0 fn2-checkpoint-page) 0))))
       (mv :pending fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes))
      ((unless (if (equal role 3)
                   (and (< ordinal pages)
                        (equal (fn2-event-build-directory-completed 0 fn2-event-build)
                               (* (- pages (+ ordinal 1)) *fn2-format-page-size*)))
                 (and (equal ordinal 0) (equal (fn2-event-build-peak 0 fn2-event-build) 60)
                      (equal (fn2-event-build-frontier-completed 0 fn2-event-build) 0)
                      (equal (fn2-event-build-directory-completed 0 fn2-event-build) (* pages *fn2-format-page-size*)))))
       (mv :coverage fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes))
      (frontier-pages (+ 1 (fn2-release-inventory-build-pages 0 fn2-release-inventory-build)))
      ((unless (or (equal role 3)
       (fn2-release-inventory-complete-p fn2-release-inventory-build fn2-csnapshot fn2-checkpoints
        fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified)))
       (mv :inventory fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes))
      (completed (if (equal role 3) (+ *fn2-format-page-size* (fn2-event-build-directory-completed 0 fn2-event-build))
                      (* frontier-pages *fn2-format-page-size*)))
      ((when (and (equal role 3) (posp ordinal)))
       (let ((fn2-event-build (fn2-event-build-put 0 (phase *fn2-event-build-phase-reserve*) (ordinal (- ordinal 1))
                               (child e) (has-child 1) (directory-completed completed))))
        (mv :more fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes)))
      (intended (if (equal role 3) (* pages *fn2-format-page-size*) (* frontier-pages *fn2-format-page-size*)))
      ((unless (equal completed intended)) (mv :coverage fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes))
      (fn2-checkpoint-bytes (fn2-checkpoint-map-root-hash-copy 32 0 e (* 32 r) fn2-checkpoint-page-verified fn2-checkpoint-bytes))
      (fn2-checkpoint-refs (fn2-checkpoint-refs-put r
       (storage-domain *fn2-checkpoint-served-storage-domain*) (physical-unit (* e *fn2-storage-extent-units*))
       (writer-epoch (fn2-event-build-epoch 0 fn2-event-build)) (allocation (fn2-event-build-allocation 0 fn2-event-build))
       (page-kind (if (equal role 3) *page-kind-manifest* *page-kind-merkle-node*)) (encoded-length *fn2-format-page-size*)
       (edge 0) (retained 0) (root-build-token token) (root-source-complete 1)
       (root-intended-bytes intended) (root-completed-bytes completed)))
      (fn2-event-build (if (equal role 3)
       (fn2-event-build-put 0 (phase *fn2-event-build-phase-inventory-begin*) (role 4) (ordinal 0) (has-child 0)
         (directory-completed completed) (zero 0) (peak 0))
       (fn2-event-build-put 0 (phase *fn2-event-build-phase-done*) (frontier-completed completed)))))
  (mv (if (equal role 3) :more :done) fn2-event-build fn2-checkpoint-refs fn2-checkpoint-bytes)))

; Parent source actor dispatches this bounded source step, then BIND/TAKE and
; parks at :wait until the actual physical worker returns the owned workspace.
; Field stripe identity is derived from the served resource table here.
(defun fn2-event-build-source-step (budget fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-commit-root
                                   fn2-checkpoint-refs fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops
                                   fn2-checkpoint-page-verified fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-control fn2-checkpoint-summary-authority fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-release-inventory-build)
 (declare (xargs :stobjs (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-commit-root fn2-checkpoint-refs
                          fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoint-page-verified
                          fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-control fn2-checkpoint-summary-authority fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-release-inventory-build) :verify-guards nil
  :guard (and (fn2-event-build-wfp fn2-event-build) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-commit-root-wfp fn2-commit-root) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-ops-wfp fn2-ops) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-mk-wfp fn2-mk) (fn2-fc-wfp fn2-fc) (fn2-digests-wfp fn2-digests) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-restore-events-wfp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work) (fn2-event-buildp fn2-event-build) (fn2-event-readp fn2-event-read) (fn2-csnapshotp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-commit-rootp fn2-commit-root) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-opsp fn2-ops) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-mkp fn2-mk) (fn2-fcp fn2-fc) (fn2-digestsp fn2-digests) (fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-controlp fn2-control) (fn2-checkpoint-summary-authorityp fn2-checkpoint-summary-authority) (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-restore-eventsp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-workp fn2-checkpoint-restore-events-work) (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build))))
 (b* (((unless (fn2-event-build-ownerp fn2-event-build fn2-csnapshot fn2-checkpoints))
       (mv :owner fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control))
      (phase (fn2-event-build-phase 0 fn2-event-build))
      (base (* 128 (fn2-b-event-row (fn2-fc-rows fn2-fc))))
      (budget (min 4096 (nfix budget))))
  (cond
   ((member-equal phase (list *fn2-event-build-phase-claim-zero* *fn2-event-build-phase-zero*))
    (mv-let (code fn2-event-build fn2-pool) (fn2-event-build-zero-step budget fn2-event-build fn2-csnapshot fn2-checkpoints fn2-pool)
     (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))
   ((member-equal phase (list *fn2-event-build-phase-claims* *fn2-event-build-phase-entries*))
    (mv-let (code fn2-event-build fn2-extents fn2-alloc-edges fn2-fields fn2-pool)
     (fn2-event-build-entry-step budget base fn2-event-build fn2-csnapshot fn2-checkpoints fn2-commit-root
      fn2-extents fn2-alloc-edges fn2-ops fn2-fc fn2-digests fn2-fields fn2-pool fn2-checkpoint-summary-authority fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
     (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))
   ((equal phase *fn2-event-build-phase-reserve*)
    (if (zp budget) (mv :yield fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)
     (mv-let (code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-control)
      (fn2-event-build-reserve fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-control)
      (mv (if (eq code :ok) :more code) fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control))))
   ((equal phase *fn2-event-build-phase-directory-header*)
    (mv-let (code fn2-event-build fn2-fields fn2-pool)
     (fn2-event-build-directory-header budget base fn2-event-build fn2-csnapshot fn2-checkpoints
      fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-fields fn2-pool)
     (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))
   ((equal phase *fn2-event-build-phase-frontier-header*)
    (mv-let (code fn2-event-build fn2-fields fn2-pool)
     (fn2-event-build-frontier-header budget base fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints
      fn2-checkpoint-refs fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-release-inventory-build)
     (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))
   ((equal phase *fn2-event-build-phase-peaks*)
    (mv-let (code fn2-event-build fn2-pool)
     (fn2-event-build-peak-step budget fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-mk fn2-fc fn2-digests fn2-pool)
     (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))
   ((equal phase *fn2-event-build-phase-physical-header*)
    (mv-let (code fn2-event-build fn2-fields fn2-pool)
     (fn2-event-build-physical-header budget base fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool)
     (mv code fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))
   (t (mv (cond ((equal phase *fn2-event-build-phase-page*) :page) ((equal phase *fn2-event-build-phase-bound*) :wait)
                ((equal phase *fn2-event-build-phase-done*) :done) (t :uncertain))
          fn2-event-build fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-fields fn2-pool fn2-control)))))

(fn2-event-build-preserves fn2-event-build-begin
 (c token slot gen scratch sgen okind oslot ogen
                             fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                             fn2-mk fn2-fc fn2-digests fn2-pool)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER")))

(fn2-event-build-preserves fn2-event-build-reserve
 (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-control)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-checkpoint-construction 2 :prefix "-REGISTRY") (fn2-extents 3 :prefix "-EXTENTS") (fn2-control 4 :prefix "-CONTROL")))

(fn2-event-build-preserves fn2-event-build-zero-step
 (budget fn2-event-build fn2-csnapshot fn2-checkpoints fn2-pool)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-pool 2 :prefix "-POOL")))

(fn2-event-build-preserves fn2-event-build-entry-step
 (budget base fn2-event-build fn2-csnapshot fn2-checkpoints fn2-commit-root
                                  fn2-extents fn2-alloc-edges fn2-ops fn2-fc fn2-digests fn2-fields fn2-pool fn2-checkpoint-summary-authority fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-extents 2 :prefix "-EXTENTS") (fn2-alloc-edges 3 :prefix "-EDGES") (fn2-fields 4 :prefix "-FIELDS") (fn2-pool 5 :prefix "-POOL")))

(fn2-event-build-preserves fn2-event-build-directory-header
 (budget base fn2-event-build fn2-csnapshot fn2-checkpoints
                                        fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified fn2-fields fn2-pool)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-fields 2 :prefix "-FIELDS") (fn2-pool 3 :prefix "-POOL")))

(fn2-event-build-preserves fn2-event-build-frontier-header
 (budget base fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints
                                       fn2-checkpoint-refs fn2-checkpoint-construction fn2-extents fn2-checkpoint-page-verified
                                       fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-release-inventory-build)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-fields 2 :prefix "-FIELDS") (fn2-pool 3 :prefix "-POOL")) :hyps ((fn2-event-buildp fn2-event-build) (fn2-event-build-wfp fn2-event-build) (fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build)))

(fn2-event-build-preserves fn2-event-build-peak-step
 (budget fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-mk fn2-fc fn2-digests fn2-pool)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-pool 2 :prefix "-POOL")))

(fn2-event-build-preserves fn2-event-build-physical-header
 (budget base fn2-event-build fn2-csnapshot fn2-checkpoints
                                       fn2-checkpoint-construction fn2-extents fn2-fields fn2-pool)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-fields 2 :prefix "-FIELDS") (fn2-pool 3 :prefix "-POOL")))

(fn2-event-build-preserves fn2-event-build-bind-page
 (fn2-event-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents
                                 fn2-checkpoint-page fn2-checkpoint-page-verified fn2-pool fn2-fc fn2-fields)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-checkpoint-page 2 :prefix "-PAGE")))

(fn2-event-build-preserves fn2-event-build-consume-page
 (fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                                    fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-mk fn2-fc fn2-digests fn2-pool fn2-release-inventory-build)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-checkpoint-refs 2 :prefix "-REFS") (fn2-checkpoint-bytes 3 :prefix "-BYTES")) :hyps ((fn2-event-buildp fn2-event-build) (fn2-event-build-wfp fn2-event-build) (fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-pagep fn2-checkpoint-page) (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build)))

(fn2-event-build-preserves fn2-event-build-source-step
 (budget fn2-event-build fn2-event-read fn2-csnapshot fn2-checkpoints fn2-commit-root
                                   fn2-checkpoint-refs fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops
                                   fn2-checkpoint-page-verified fn2-mk fn2-fc fn2-digests fn2-fields fn2-pool fn2-control fn2-checkpoint-summary-authority fn2-checkpoint-bytes fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-release-inventory-build)
 :carriers ((fn2-event-build 1 :prefix "-BUILDER") (fn2-checkpoint-construction 2 :prefix "-REGISTRY") (fn2-extents 3 :prefix "-EXTENTS") (fn2-alloc-edges 4 :prefix "-EDGES") (fn2-fields 5 :prefix "-FIELDS") (fn2-pool 6 :prefix "-POOL") (fn2-control 7 :prefix "-CONTROL")) :hyps ((fn2-event-buildp fn2-event-build) (fn2-event-build-wfp fn2-event-build) (fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read) (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-commit-rootp fn2-commit-root) (fn2-commit-root-wfp fn2-commit-root) (fn2-checkpoint-refsp fn2-checkpoint-refs) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs) (fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents) (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops) (fn2-checkpoint-page-verifiedp fn2-checkpoint-page-verified) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-mkp fn2-mk) (fn2-mk-wfp fn2-mk) (fn2-fcp fn2-fc) (fn2-fc-wfp fn2-fc) (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (fn2-controlp fn2-control) (fn2-control-wfp fn2-control) (fn2-checkpoint-summary-authorityp fn2-checkpoint-summary-authority) (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-checkpoint-bytesp fn2-checkpoint-bytes) (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-restore-eventsp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-wfp fn2-checkpoint-restore-events) (fn2-checkpoint-restore-events-workp fn2-checkpoint-restore-events-work) (fn2-checkpoint-restore-events-work-wfp fn2-checkpoint-restore-events-work) (fn2-release-inventory-buildp fn2-release-inventory-build) (fn2-release-inventory-build-wfp fn2-release-inventory-build)))
