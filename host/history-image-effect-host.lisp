; Actual native image executor consumes these core projections under the
; extent/pool serialization. No publication or open-file policy lives here.
(in-package "ACL2")
(include-book "history-image-producer-host")
(include-book "../books/history-image-effect-boundary")

(defun fn-owner-history-image-effect-plan (c effect stage fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (if (eq (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool)
      (fn-hie-plan c effect stage (fn-owner-page-read-ledger fn-page-read-pool))
    '(:refused :maintenance-resources-unavailable)))
(defun fn-owner-history-image-effect-result (c effect stage got status bytes fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (fn-hie-observation c effect stage (fn-owner-page-read-ledger fn-page-read-pool)
                      got status bytes))
(defun fn-owner-history-image-effect-read-count (c effect stage got status fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (fn-hie-read-count c effect stage (fn-owner-page-read-ledger fn-page-read-pool) got status))
(defun fn-owner-history-image-effect-byte (c effect stage i fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb
                                           fn-page-read-pool)
  (declare (xargs :stobjs (fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb fn-page-read-pool)
                  :guard (and (natp i) (< i 16384))))
  (fn-hie-page-byte c effect stage (fn-owner-page-read-ledger fn-page-read-pool) i
                   fn-hpq0 fn-hpq1 fn-hpq2 fn-hpq3 fn-hpb))
