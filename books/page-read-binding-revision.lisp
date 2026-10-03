; SAME pool DATA6 publication. Genuine runtime source installation is separate.
(in-package "ACL2")
(include-book "page-read-pool-state")

; Fixed DATA position; an old DATA5 record has revision zero. This getter
; performs no scan of binding rows and establishes no installation authority.
(defun fn-prb-data-revision (data)
  (declare (xargs :guard t))
  (let ((revision (fn-prl-nth 5 data)))
    (if revision revision 0)))

(defun fn-owner-page-read-binding-revision (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prb-data-revision (fn-prp-data fn-page-read-pool)))

; Internal counter-only composition. The proposed next ledger's binding field
; is NEVER installed. The current actual root is selected inside the operation.
; Each caller still needs a theorem showing its semantic transition changes
; counters only; this helper is not a public debit/nonce/admission authority.
(defun fn-prb-keep-current-bindings (next current)
  (declare (xargs :guard t))
  (fn-prl-build (fn-prl-nth 0 next) (fn-prl-nth 1 next)
                (fn-prl-nth 2 next) (fn-prl-nth 3 current)
                (fn-prl-nth 4 next)))

 ; DATA6 constructor used by the sole installer and every publication.
(defun fn-prb-data6 (ledger data revision)
 (declare (xargs :guard t))
 (append (list ledger (fn-prl-nth 1 data) (fn-prl-nth 2 data)
               (fn-prl-nth 3 data) (fn-prl-nth 4 data) revision)
         (fn-prp-metadata-tail 6 data)))

; Internal metadata publication, not allocation/nonce authority. The caller
; proves its semantic transition counter-only and obtains actual BODY funding.
; Intent retains both graphs BEFORE any ledger publication. Unknown raw cuts
; leave recovery mode and forbid another issuer; no rollback/retry is inferred.
(defun fn-owner-page-read-counter-publish (next fn-page-read-pool)
 (declare (xargs :stobjs fn-page-read-pool))
 (let* ((data (fn-prp-data fn-page-read-pool))
        (mode (fn-prp-mode fn-page-read-pool))
        (epoch-mode (fn-prp-alloc-mode fn-page-read-pool))
        (revision (fn-prb-data-revision data)))
  (if (not (and data (natp revision) (eq mode :served)
                (member-eq epoch-mode '(:active :draining))))
   (mv :counter-publication-unavailable fn-page-read-pool)
   (let* ((ledger (fn-prb-keep-current-bindings next (fn-prl-nth 0 data)))
          (intent (list :counter-publishing mode epoch-mode data ledger revision))
          (fn-page-read-pool (update-fn-prp-mode intent fn-page-read-pool))
          (fn-page-read-pool (update-fn-prp-alloc-mode :recovery fn-page-read-pool))
          (fn-page-read-pool (update-fn-prp-data (fn-prb-data6 ledger data revision) fn-page-read-pool))
          (fn-page-read-pool (update-fn-prp-alloc-mode epoch-mode fn-page-read-pool))
          (fn-page-read-pool (update-fn-prp-mode mode fn-page-read-pool)))
    (mv :published fn-page-read-pool)))))

(defthm fn-prb-counter-composition-retains-binding-root-by-definition
  (equal (fn-prl-nth 3 (fn-prb-keep-current-bindings next current))
         (fn-prl-nth 3 current))
  :hints (("Goal" :in-theory (enable fn-prb-keep-current-bindings
                                   fn-prl-build fn-prl-nth))))

(defthm fn-owner-page-read-counter-publication-preserves-revision-by-definition
  (equal (fn-owner-page-read-binding-revision
          (mv-nth 1 (fn-owner-page-read-counter-publish next fn-page-read-pool)))
         (fn-owner-page-read-binding-revision fn-page-read-pool))
  :hints (("Goal" :in-theory (enable fn-owner-page-read-counter-publish
                                   fn-owner-page-read-binding-revision
                                   fn-prb-data-revision fn-prl-nth))))

; The legacy pool-only keeper cannot discard a refusal. Every actual caller
; must migrate to a status publisher and retain/fence any preexisting actor
; mutation on unavailable/stale publication. No DATA6 activation with oldwriters.
; Source/constructor census and matched raw publication cuts remain required.

(defthm fn-owner-page-read-counter-publication-preserves-bindings
 (equal (fn-prl-nth 3 (fn-owner-page-read-ledger
                      (mv-nth 1 (fn-owner-page-read-counter-publish next fn-page-read-pool))))
        (fn-prl-nth 3 (fn-owner-page-read-ledger fn-page-read-pool)))
 :hints (("Goal" :in-theory (enable fn-owner-page-read-counter-publish
                                   fn-owner-page-read-ledger fn-prb-data6
                                   fn-prb-keep-current-bindings fn-prl-build fn-prl-nth))))
(defthm fn-owner-page-read-counter-publication-refusal-keeps-pool
 (implies (not (equal (mv-nth 0 (fn-owner-page-read-counter-publish next fn-page-read-pool)) :published))
          (equal (mv-nth 1 (fn-owner-page-read-counter-publish next fn-page-read-pool)) fn-page-read-pool))
 :hints (("Goal" :in-theory (enable fn-owner-page-read-counter-publish))))
