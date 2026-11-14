; Complete child results, including protected sibling partition and control.
; This fixture starts from the actual child creators, then installs explicit
; typed partition counters. It does not claim a reachable whole-core state.
(in-package "ACL2")
(include-book "../books/machine-reservations")
(include-book "column-snapshot-support")

(make-event
 (let* ((world (w state))
        (events (append (fn2-test-column-snapshot-events 'fn2-machines world)
                        (fn2-test-column-snapshot-events 'fn2-control world))))
   (value `(progn
             (local (deftheory fn2-reservation-snapshot-base (current-theory :here)))
             (encapsulate () (local (in-theory nil)) ,@events)
             (local (in-theory (theory 'fn2-reservation-snapshot-base)))))))

(defun fn2-reservation-child-control-run (takep mutation fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-machines fn2-control) :verify-guards nil))
  (b* ((overflow-active (and takep (eq mutation :without-reservation)))
       (fn2-machines (update-fn2-machines-connection-counti
                      0 (if overflow-active 4294967295 2) fn2-machines))
       (fn2-machines (update-fn2-machines-active-counti
                      0 (if overflow-active 4294967295 1) fn2-machines))
       (fn2-machines (update-fn2-machines-admission-creditsi
                      0 (if (and (not takep) (eq mutation :without-reservation))
                            4294967295 1) fn2-machines))
       (fn2-machines (update-fn2-machines-free-headi 0 9 fn2-machines))
       ; A populated unrelated partition makes its frame observable.
       (fn2-machines (update-fn2-machines-connection-counti 1 5 fn2-machines))
       (fn2-machines (update-fn2-machines-active-counti 1 2 fn2-machines))
       (fn2-machines (update-fn2-machines-admission-creditsi 1 3 fn2-machines))
       (fn2-machines (update-fn2-machines-free-headi 1 44 fn2-machines))
       (before (fn2-test-table-snapshot-fn2-machines fn2-machines))
       (ctl-before (fn2-test-table-snapshot-fn2-control fn2-control))
       (base-h (and (fn2-machinesp fn2-machines) (fn2-machines-wfp fn2-machines)
                    (fn2-controlp fn2-control) (fn2-control-wfp fn2-control)
                    (unsigned-byte-p 32 3) (unsigned-byte-p 32 9)
                    (< 0 (fn2-machines-active-counti 0 fn2-machines))
                    (< 0 (fn2-machines-admission-creditsi 0 fn2-machines))))
       (reserved (fn2-machines-partition-reservedp 0 fn2-machines))
       (expected (if takep
                     (fn2-machines-install-list-expected 0 3 9 t before ctl-before)
                   (fn2-machines-reclaim-list-expected 3 0 nil before ctl-before)))
       ((mv fn2-machines fn2-control)
        (if takep (fn2-machines-partition-install 0 3 9 t fn2-machines fn2-control)
          (fn2-machines-reclaim 3 0 nil fn2-machines fn2-control)))
       (fn2-machines (if (eq mutation :sibling)
                         (update-fn2-machines-connection-counti 1 7 fn2-machines)
                       fn2-machines))
       (observed (list (fn2-test-table-snapshot-fn2-machines fn2-machines)
                       (fn2-test-table-snapshot-fn2-control fn2-control)))
       (whole-c (equal observed expected)))
    (mv (and base-h
             (if (eq mutation :without-reservation)
                 (and (not reserved) (not whole-c)
                      (equal (fn2-control-stop fn2-control) 1)
                      (equal (fn2-control-stop-reason fn2-control) *fn2-stop-reason-machine-write*))
               (and reserved
                    (if (eq mutation :sibling) (not whole-c)
                      (and whole-c (fn2-machines-partition-reservedp 0 fn2-machines))))))
        fn2-machines fn2-control)))
(defun fn2-reservation-child-control (takep mutation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-machines
    (mv-let (yes fn2-machines)
      (with-local-stobj fn2-control
        (mv-let (yes fn2-machines fn2-control)
          (fn2-reservation-child-control-run takep mutation fn2-machines fn2-control)
          (mv yes fn2-machines)))
      yes)))
(assert-event (and (fn2-reservation-child-control nil nil)
                   (fn2-reservation-child-control t nil)))
(assert-event (and (fn2-reservation-child-control nil :sibling)
                   (fn2-reservation-child-control t :sibling)))
; Removing conservation permits the checked credit refund to fail after
; the free-head write. Actual reclaim still decreases active: no rollback.
(assert-event (fn2-reservation-child-control nil :without-reservation))
; Installation can instead overflow active while credits remain positive.
; The checked increment refuses; the later credit debit/wake still occur.
(assert-event (fn2-reservation-child-control t :without-reservation))
