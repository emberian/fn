; Actual generated header codec and physical namespace roundtrip only.
; This does not assert the cold reader's physical authentication antecedent.
; Runnable source, unexecuted under the source-only grant.
(in-package "ACL2")
(include-book "../books/event-archive-cold-header")
(defun fn2-eahcu-body (fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* ((fn2-fields (fn2-fields-init *fn2-event-archive-header-num-fields* fn2-fields))
      (fn2-pool (fn2-pool-init '((2 . 4096)) 1 100 fn2-pool))
      ((mv cs scratch sg fn2-pool) (fn2-pool-reserve 0 1 2 3 fn2-pool))
      ((mv cp page pg fn2-pool) (fn2-pool-reserve 0 1 2 3 fn2-pool))
      ((mv cz fn2-pool) (fn2-run-zero 64 scratch sg 0 1 2 3 fn2-pool))
      (fn2-fields (fn2-event-archive-header-bind 0 *checkpoint-event-archive-kind-canonical-member-archive* 1
       9 123 456 7 11 scratch sg 0 1 11 1 9 1 1 0 32 2 4 *page-kind-manifest* *fn2-format-page-size* scratch sg 32 fn2-fields))
      ((mv ce next fn2-pool) (fn2-event-archive-header-encode 0 page pg *fn2-event-archive-header-start* 1 2 3 fn2-fields fn2-pool))
      ((mv cd end fn2-fields) (fn2-event-archive-header-decode 0 page pg *fn2-event-archive-header-start* next 1 2 3 fn2-fields fn2-pool)))
  (mv (and (eq cs :ok) (eq cp :ok) (eq cz :ok) (eq ce :ok) (eq cd :ok) (= next end)
           (= (fn2-fields-value *fn2-event-archive-header-field-history* fn2-fields) 123)
           (= (fn2-fields-value *fn2-event-archive-header-field-incarnation* fn2-fields) 456)
           (= (fn2-fields-value *fn2-event-archive-header-field-cut-commit* fn2-fields) 7)
           (= (fn2-fields-value *fn2-event-archive-header-field-cut-event* fn2-fields) 11)
           (= (fn2-fields-value *fn2-event-archive-header-field-manifest-run* fn2-fields) 9)
           (= (fn2-fields-value *fn2-event-archive-header-field-manifest-physical-unit* fn2-fields) 32)
           (= (fn2-fields-ref-slot *fn2-event-archive-header-field-cut-seal* fn2-fields) page)
           (= (fn2-fields-ref-gen *fn2-event-archive-header-field-manifest-expected-hash* fn2-fields) pg)
           (= (fn2-fields-ref-len *fn2-event-archive-header-field-manifest-expected-hash* fn2-fields) 32)) fn2-fields fn2-pool)))
(defun fn2-eahcu-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (answer fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (answer fn2-fields fn2-pool) (fn2-eahcu-body fn2-fields fn2-pool)
     (mv answer fn2-fields))) answer)))
(assert-event (fn2-eahcu-test))
