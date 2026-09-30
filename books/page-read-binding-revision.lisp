; Owned additive helper candidate. Not an admitted/installed interface.
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

(defun fn-owner-page-read-counter-publish (next fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let* ((data (fn-prp-data fn-page-read-pool))
         (revision (fn-prb-data-revision data)))
    (if (not (and data (natp revision)))
        (mv :unavailable fn-page-read-pool)
      (let* ((ledger (fn-prb-keep-current-bindings next (fn-prl-nth 0 data)))
             (new-data (list ledger (fn-prl-nth 1 data) (fn-prl-nth 2 data)
                             (fn-prl-nth 3 data) (fn-prl-nth 4 data) revision))
             (fn-page-read-pool (update-fn-prp-data new-data fn-page-read-pool)))
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

; Binding-dirty publisher is deliberately not supplied here. It must return
; word/pool, validate the genuine installed immediate domain BEFORE successor
; addition, persist actual actor commit intent and qualify the raw data-store
; cut. Existing pool-only keeper cannot discard refusal. Do not migrate callers
; or publish DATA6 while an active old keeper can truncate the revision.
