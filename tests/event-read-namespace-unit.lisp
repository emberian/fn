; SOURCE control over the actual frame producer and namespace-hint decoder.
; No hash/fence/physical completion or cold source acceptance is claimed here.
(in-package "ACL2")
(include-book "c-snapshot-unit")
(include-book "../books/event-read-verify")
(include-book "../books/commit-format")
(defun fn2-ern-body (records fn2-event-read fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-event-read fn2-fields fn2-pool) :verify-guards nil))
 (b* ((fn2-event-read (fn2-event-read-init 1 fn2-event-read))
      (fn2-fields (fn2-fields-init 128 fn2-fields))
      (fn2-pool (fn2-pool-init '((1 . 4096)) 1 100 fn2-pool))
      ((mv reserved slot gen fn2-pool) (fn2-pool-reserve 0 7 0 1 fn2-pool))
      ((mv zeroed fn2-pool) (fn2-run-zero 4096 slot gen 0 7 0 1 fn2-pool))
      ; Physical journal pair29/31 differs from logical origin101/103/107.
      ((mv packed end fn2-fields fn2-pool)
       (fn2-commit-pack :frame (if records 1 2) 0 slot gen 0 slot gen
         2 5 7 11 13 1 7 0 1 101 103 107 29 31 fn2-fields fn2-pool))
      (fn2-event-read (fn2-event-read-put 0
       (phase *fn2-event-read-phase-frame-seal*) (pending 0) (slot slot) (gen gen)
       (owner-kind 7) (owner-slot 0) (owner-gen 1) (field-base 0)))
      ((mv code fn2-event-read fn2-fields) (fn2-event-read-namespace fn2-event-read fn2-fields fn2-pool)))
  (mv (and (eq reserved :ok) (eq zeroed :ok) (eq packed :ok) (< end 4096)
           (= (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-frame-seal*)
           (if records
               (and (eq code :frame) (= (fn2-event-read-journal-history 0 fn2-event-read) 0) (= (fn2-event-read-journal-incarnation 0 fn2-event-read) 0))
             (and (eq code :ok) (= (fn2-event-read-journal-history 0 fn2-event-read) 29) (= (fn2-event-read-journal-incarnation 0 fn2-event-read) 31))))
      fn2-event-read fn2-fields fn2-pool)))
(defun fn2-ern-test (records)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-event-read fn2-fields fn2-pool)
  (fn2-ern-body records fn2-event-read fn2-fields fn2-pool)))
(assert-event (fn2-ern-test nil))
(assert-event (fn2-ern-test t))
