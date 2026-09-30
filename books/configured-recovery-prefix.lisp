; Same-pass prefix storage for configured recovery. This is a FILES-shaped
; lookup projection, never a persisted Store or a durable acceptance result.
; Source assembly only; guarded caller, prefix relation, allocation and seeded
; checkpoint-history initialization remain open.
(in-package "ACL2")
(include-book "history-columns-relation")

(defun fn-crp-counted-fieldp (field)
 (declare (xargs :guard t))
 (if (fn-sfr-basedp field)
     (or (null (fn-sfr-suffix field)) (fn-sl-snoc-formp (fn-sfr-suffix field)))
   (or (null field) (fn-sl-snoc-formp field))))

(defun fn-crp-append (prefix-files row fn-hist)
 (declare (xargs :stobjs fn-hist :verify-guards nil :guard t))
 ; Reject the legacy raw-list branch before COUNT can walk its history.
 (if (not (fn-crp-counted-fieldp (fn-sf-records-field prefix-files)))
  (mv :unavailable prefix-files fn-hist)
 (let ((count (fn-sf-records-count prefix-files)))
  ; Refuse before either store append or index mutation. These scalar gates
  ; do not establish the row's physical/source provenance.
  (if (and (natp count)
           (equal (fn-hist-count fn-hist) count)
           (equal (fn-store-event-sequence row) count))
   (let* ((next-field (fn-sfr-snoc (fn-sf-records-field prefix-files) row))
          (next-files
           (fn-sf-make-fields (fn-sf-phase prefix-files)
            (fn-sf-frontier prefix-files) (fn-sf-frontier-candidate prefix-files)
            next-field (fn-sf-record-candidate prefix-files)
            (fn-sf-completion prefix-files) (fn-sf-successes-field prefix-files)
            (fn-sf-barriers prefix-files)))
          (fn-hist (fn-hist-append row fn-hist)))
    (mv :appended next-files fn-hist))
   (mv :unavailable prefix-files fn-hist)))))
